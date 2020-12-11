use bellman::pairing::{
    Engine,
};

use bellman::pairing::ff::{
    Field,
    PrimeField
};

use bellman::{
    SynthesisError,
    ConstraintSystem,
    LinearCombination
};

use super::boolean::{
    Boolean,
    AllocatedBit
};

use super::multieq::MultiEq;

/// Represents an interpretation of 64 `Boolean` objects as an
/// unsigned integer.
#[derive(Clone)]
pub struct UInt64 {
    // Least significant bit first
    bits: Vec<Boolean>,
    value: Option<u64>
}

impl UInt64 {
    /// Construct a constant `UInt64` from a `u64`
    pub fn constant(value: u64) -> Self
    {
        let mut bits = Vec::with_capacity(64);

        let mut tmp = value;
        for _ in 0..64 {
            if tmp & 1 == 1 {
                bits.push(Boolean::constant(true))
            } else {
                bits.push(Boolean::constant(false))
            }

            tmp >>= 1;
        }

        UInt64 {
            bits: bits,
            value: Some(value)
        }
    }

    /// Allocate a `UInt64` in the constraint system
    pub fn alloc<E, CS>(
        mut cs: CS,
        value: Option<u64>
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let values = match value {
            Some(mut val) => {
                let mut v = Vec::with_capacity(64);

                for _ in 0..64 {
                    v.push(Some(val & 1 == 1));
                    val >>= 1;
                }

                v
            },
            None => vec![None; 64]
        };

        let bits = values.into_iter()
                         .enumerate()
                         .map(|(i, v)| {
                            Ok(Boolean::from(AllocatedBit::alloc(
                                cs.namespace(|| format!("allocated bit {}", i)),
                                v
                            )?))
                         })
                         .collect::<Result<Vec<_>, SynthesisError>>()?;

        Ok(UInt64 {
            bits: bits,
            value: value
        })
    }

    pub fn into_bits_be(&self) -> Vec<Boolean> {
        self.bits.iter().rev().cloned().collect()
    }

    pub fn from_bits_be(bits: &[Boolean]) -> Self {
        assert_eq!(bits.len(), 64);

        let mut value = Some(0u64);
        for b in bits {
            value.as_mut().map(|v| *v <<= 1);

            match b.get_value() {
                Some(true) => { value.as_mut().map(|v| *v |= 1); },
                Some(false) => {},
                None => { value = None; }
            }
        }

        UInt64 {
            value: value,
            bits: bits.iter().rev().cloned().collect()
        }
    }


    /// Turns this `UInt64` into its little-endian byte order representation.
    pub fn into_bits(&self) -> Vec<Boolean> {
        self.bits.clone()
    }

    /// Converts a little-endian byte order representation of bits into a
    /// `UInt64`.
    pub fn from_bits(bits: &[Boolean]) -> Self
    {
        assert_eq!(bits.len(), 64);

        let new_bits = bits.to_vec();

        let mut value = Some(0u64);
        for b in new_bits.iter().rev() {
            value.as_mut().map(|v| *v <<= 1);

            match b {
                &Boolean::Constant(b) => {
                    if b {
                        value.as_mut().map(|v| *v |= 1);
                    }
                },
                &Boolean::Is(ref b) => {
                    match b.get_value() {
                        Some(true) => { value.as_mut().map(|v| *v |= 1); },
                        Some(false) => {},
                        None => { value = None }
                    }
                },
                &Boolean::Not(ref b) => {
                    match b.get_value() {
                        Some(false) => { value.as_mut().map(|v| *v |= 1); },
                        Some(true) => {},
                        None => { value = None }
                    }
                }
            }
        }

        UInt64 {
            value: value,
            bits: new_bits
        }
    }

    pub fn rotr(&self, by: usize) -> Self {
        let by = by % 64;

        let new_bits = self.bits.iter()
                                .skip(by)
                                .chain(self.bits.iter())
                                .take(64)
                                .cloned()
                                .collect();

        UInt64 {
            bits: new_bits,
            value: self.value.map(|v| v.rotate_right(by as u32))
        }
    }

    pub fn shr(&self, by: usize) -> Self {
        let by = by % 64;

        let fill = Boolean::constant(false);

        let new_bits = self.bits
                           .iter() // The bits are least significant first
                           .skip(by) // Skip the bits that will be lost during the shift
                           .chain(Some(&fill).into_iter().cycle()) // Rest will be zeros
                           .take(64) // Only 64 bits needed!
                           .cloned()
                           .collect();

        UInt64 {
            bits: new_bits,
            value: self.value.map(|v| v >> by as u64)
        }
    }

    fn triop<E, CS, F, U>(
        mut cs: CS,
        a: &Self,
        b: &Self,
        c: &Self,
        tri_fn: F,
        circuit_fn: U
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>,
              F: Fn(u64, u64, u64) -> u64,
              U: Fn(&mut CS, usize, &Boolean, &Boolean, &Boolean) -> Result<Boolean, SynthesisError>
    {
        let new_value = match (a.value, b.value, c.value) {
            (Some(a), Some(b), Some(c)) => {
                Some(tri_fn(a, b, c))
            },
            _ => None
        };

        let bits = a.bits.iter()
                            .zip(b.bits.iter())
                            .zip(c.bits.iter())
                            .enumerate()
                            .map(|(i, ((a, b), c))| circuit_fn(&mut cs, i, a, b, c))
                            .collect::<Result<_, _>>()?;

        Ok(UInt64 {
            bits: bits,
            value: new_value
        })
    }

    /// Compute the `maj` value (a and b) xor (a and c) xor (b and c)
    /// during SHA256.
    pub fn sha256_maj<E, CS>(
        cs: CS,
        a: &Self,
        b: &Self,
        c: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        Self::triop(cs, a, b, c, |a, b, c| (a & b) ^ (a & c) ^ (b & c),
            |cs, i, a, b, c| {
                Boolean::sha256_maj(
                    cs.namespace(|| format!("maj {}", i)),
                    a,
                    b,
                    c
                )
            }
        )
    }

    /// Compute the `ch` value `(a and b) xor ((not a) and c)`
    /// during SHA256.
    pub fn sha256_ch<E, CS>(
        cs: CS,
        a: &Self,
        b: &Self,
        c: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        Self::triop(cs, a, b, c, |a, b, c| (a & b) ^ ((!a) & c),
            |cs, i, a, b, c| {
                Boolean::sha256_ch(
                    cs.namespace(|| format!("ch {}", i)),
                    a,
                    b,
                    c
                )
            }
        )
    }

    /// XOR this `UInt64` with another `UInt64`
    pub fn xor<E, CS>(
        &self,
        mut cs: CS,
        other: &Self
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>
    {
        let new_value = match (self.value, other.value) {
            (Some(a), Some(b)) => {
                Some(a ^ b)
            },
            _ => None
        };

        let bits = self.bits.iter()
                            .zip(other.bits.iter())
                            .enumerate()
                            .map(|(i, (a, b))| {
                                Boolean::xor(
                                    cs.namespace(|| format!("xor of bit {}", i)),
                                    a,
                                    b
                                )
                            })
                            .collect::<Result<_, _>>()?;

        Ok(UInt64 {
            bits: bits,
            value: new_value
        })
    }

    /// Perform modular addition of several `UInt64` objects.
    pub fn addmany<E, CS, M>(
        mut cs: M,
        operands: &[Self]
    ) -> Result<Self, SynthesisError>
        where E: Engine,
              CS: ConstraintSystem<E>,
              M: ConstraintSystem<E, Root=MultiEq<E, CS>>
    {
        // Make some arbitrary bounds for ourselves to avoid overflows
        // in the scalar field
        assert!(E::Fr::NUM_BITS >= 128);
        assert!(operands.len() >= 2); // Weird trivial cases that should never happen
        assert!(operands.len() <= 10);

        // Compute the maximum value of the sum so we allocate enough bits for
        // the result
        let mut max_value = (operands.len() as u128) * (u64::max_value() as u128);

        // Keep track of the resulting value
        let mut result_value = Some(0u128);

        // This is a linear combination that we will enforce to equal the
        // output
        let mut lc = LinearCombination::zero();

        let mut all_constants = true;

        // Iterate over the operands
        for op in operands {
            // Accumulate the value
            match op.value {
                Some(val) => {
                    result_value.as_mut().map(|v| *v += val as u128);
                },
                None => {
                    // If any of our operands have unknown value, we won't
                    // know the value of the result
                    result_value = None;
                }
            }

            // Iterate over each bit of the operand and add the operand to
            // the linear combination
            let mut coeff = E::Fr::one();
            for bit in &op.bits {
                lc = lc + &bit.lc(CS::one(), coeff);

                all_constants &= bit.is_constant();

                coeff.double();
            }
        }

        // The value of the actual result is modulo 2^64
        let modular_value = result_value.map(|v| v as u64);

        if all_constants && modular_value.is_some() {
            // We can just return a constant, rather than
            // unpacking the result into allocated bits.

            return Ok(UInt64::constant(modular_value.unwrap()));
        }

        // Storage area for the resulting bits
        let mut result_bits = vec![];

        // Linear combination representing the output,
        // for comparison with the sum of the operands
        let mut result_lc = LinearCombination::zero();

        // Allocate each bit of the result
        let mut coeff = E::Fr::one();
        let mut i = 0;
        while max_value != 0 {
            // Allocate the bit
            let b = AllocatedBit::alloc(
                cs.namespace(|| format!("result bit {}", i)),
                result_value.map(|v| (v >> i) & 1 == 1)
            )?;

            // Add this bit to the result combination
            result_lc = result_lc + (coeff, b.get_variable());

            result_bits.push(b.into());

            max_value >>= 1;
            i += 1;
            coeff.double();
        }

        // Enforce equality between the sum and result
        cs.get_root().enforce_equal(i, &lc, &result_lc);

        // Discard carry bits that we don't care about
        result_bits.truncate(64);

        Ok(UInt64 {
            bits: result_bits,
            value: modular_value
        })
    }
}

#[cfg(test)]
mod test {
    use rand::{XorShiftRng, SeedableRng, Rng};
    use ::circuit::boolean::{Boolean};
    use super::{UInt64};
    use bellman::pairing::bls12_381::{Bls12};
    use bellman::pairing::ff::{Field};
    use ::circuit::test::*;
    use bellman::{ConstraintSystem};
    use circuit::multieq::MultiEq;

    #[test]
    fn test_uint64_from_bits_be() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0653]);

        for _ in 0..1000 {
            let v = (0..64).map(|_| Boolean::constant(rng.gen())).collect::<Vec<_>>();

            let b = UInt64::from_bits_be(&v);

            for (i, bit) in b.bits.iter().enumerate() {
                match bit {
                    &Boolean::Constant(bit) => {
                        assert!(bit == ((b.value.unwrap() >> i) & 1 == 1));
                    },
                    _ => unreachable!()
                }
            }

            let expected_to_be_same = b.into_bits_be();

            for x in v.iter().zip(expected_to_be_same.iter())
            {
                match x {
                    (&Boolean::Constant(true), &Boolean::Constant(true)) => {},
                    (&Boolean::Constant(false), &Boolean::Constant(false)) => {},
                    _ => unreachable!()
                }
            }
        }
    }

    #[test]
    fn test_uint64_from_bits() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0653]);

        for _ in 0..1000 {
            let v = (0..64).map(|_| Boolean::constant(rng.gen())).collect::<Vec<_>>();

            let b = UInt64::from_bits(&v);

            for (i, bit) in b.bits.iter().enumerate() {
                match bit {
                    &Boolean::Constant(bit) => {
                        assert!(bit == ((b.value.unwrap() >> i) & 1 == 1));
                    },
                    _ => unreachable!()
                }
            }

            let expected_to_be_same = b.into_bits();

            for x in v.iter().zip(expected_to_be_same.iter())
            {
                match x {
                    (&Boolean::Constant(true), &Boolean::Constant(true)) => {},
                    (&Boolean::Constant(false), &Boolean::Constant(false)) => {},
                    _ => unreachable!()
                }
            }
        }
    }

    #[test]
    fn test_uint64_xor() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0653]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a: u64 = rng.gen();
            let b: u64 = rng.gen();
            let c: u64 = rng.gen();

            let mut expected = a ^ b ^ c;

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = a_bit.xor(cs.namespace(|| "first xor"), &b_bit).unwrap();
            let r = r.xor(cs.namespace(|| "second xor"), &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint64_addmany_constants() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a: u64 = rng.gen();
            let b: u64 = rng.gen();
            let c: u64 = rng.gen();

            let a_bit = UInt64::constant(a);
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::constant(c);

            let mut expected = a.wrapping_add(b).wrapping_add(c);

            let r = {
                let mut cs = MultiEq::new(&mut cs);
                let r = UInt64::addmany(cs.namespace(|| "addition"), &[a_bit, b_bit, c_bit]).unwrap();
                r
            };

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(_) => panic!(),
                    &Boolean::Not(_) => panic!(),
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint64_addmany() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a: u64 = rng.gen();
            let b: u64 = rng.gen();
            let c: u64 = rng.gen();
            let d: u64 = rng.gen();

            let mut expected = (a ^ b).wrapping_add(c).wrapping_add(d);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::constant(c);
            let d_bit = UInt64::alloc(cs.namespace(|| "d_bit"), Some(d)).unwrap();

            let r = a_bit.xor(cs.namespace(|| "xor"), &b_bit).unwrap();
            let r = {
                let mut cs = MultiEq::new(&mut cs);
                let r = UInt64::addmany(cs.namespace(|| "addition"), &[r, c_bit, d_bit]).unwrap();
                r
            };

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Constant(_) => {
                        unreachable!()
                    }
                }

                expected >>= 1;
            }

            // Flip a bit and see if the addition constraint still works
            if cs.get("addition/result bit 0/boolean").is_zero() {
                cs.set("addition/result bit 0/boolean", Field::one());
            } else {
                cs.set("addition/result bit 0/boolean", Field::zero());
            }

            assert!(!cs.is_satisfied());
        }
    }

    #[test]
    fn test_uint64_rotr() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        let mut num = rng.gen();

        let a = UInt64::constant(num);

        for i in 0..64 {
            let b = a.rotr(i);
            assert_eq!(a.bits.len(), b.bits.len());

            assert!(b.value.unwrap() == num);

            let mut tmp = num;
            for b in &b.bits {
                match b {
                    &Boolean::Constant(b) => {
                        assert_eq!(b, tmp & 1 == 1);
                    },
                    _ => unreachable!()
                }

                tmp >>= 1;
            }

            num = num.rotate_right(1);
        }
    }

    #[test]
    fn test_uint64_shr() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for _ in 0..50 {
            for i in 0..60 {
                let num = rng.gen();
                let a = UInt64::constant(num).shr(i);
                let b = UInt64::constant(num >> i);

                assert_eq!(a.value.unwrap(), num >> i);

                assert_eq!(a.bits.len(), b.bits.len());
                for (a, b) in a.bits.iter().zip(b.bits.iter()) {
                    assert_eq!(a.get_value().unwrap(), b.get_value().unwrap());
                }
            }
        }
    }

    #[test]
    fn test_uint64_sha256_maj() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0653]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a: u64 = rng.gen();
            let b: u64 = rng.gen();
            let c: u64 = rng.gen();

            let mut expected = (a & b) ^ (a & c) ^ (b & c);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = UInt64::sha256_maj(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }

    #[test]
    fn test_uint64_sha256_ch() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0653]);

        for _ in 0..1000 {
            let mut cs = TestConstraintSystem::<Bls12>::new();

            let a: u64 = rng.gen();
            let b: u64 = rng.gen();
            let c: u64 = rng.gen();

            let mut expected = (a & b) ^ ((!a) & c);

            let a_bit = UInt64::alloc(cs.namespace(|| "a_bit"), Some(a)).unwrap();
            let b_bit = UInt64::constant(b);
            let c_bit = UInt64::alloc(cs.namespace(|| "c_bit"), Some(c)).unwrap();

            let r = UInt64::sha256_ch(&mut cs, &a_bit, &b_bit, &c_bit).unwrap();

            assert!(cs.is_satisfied());

            assert!(r.value == Some(expected));

            for b in r.bits.iter() {
                match b {
                    &Boolean::Is(ref b) => {
                        assert!(b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Not(ref b) => {
                        assert!(!b.get_value().unwrap() == (expected & 1 == 1));
                    },
                    &Boolean::Constant(b) => {
                        assert!(b == (expected & 1 == 1));
                    }
                }

                expected >>= 1;
            }
        }
    }
}