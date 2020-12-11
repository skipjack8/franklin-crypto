use bellman::pairing::{
    Engine,
};

use bellman::{
    SynthesisError,
    ConstraintSystem
};

use super::boolean::{
    Boolean
};

use super::uint64::{
    UInt64
};

use super::multieq::MultiEq;

/*
2.1.  Parameters
   The following table summarizes various parameters and their ranges:
                            | BLAKE2b          | BLAKE2s          |
              --------------+------------------+------------------+
               Bits in word | w = 64           | w = 32           |
               Rounds in F  | r = 12           | r = 10           |
               Block bytes  | bb = 128         | bb = 64          |
               Hash bytes   | 1 <= nn <= 64    | 1 <= nn <= 32    |
               Key bytes    | 0 <= kk <= 64    | 0 <= kk <= 32    |
               Input bytes  | 0 <= ll < 2**128 | 0 <= ll < 2**64  |
              --------------+------------------+------------------+
               G Rotation   | (R1, R2, R3, R4) | (R1, R2, R3, R4) |
                constants = | (32, 24, 16, 63) | (16, 12,  8,  7) |
              --------------+------------------+------------------+
*/

const R1: usize = 32;
const R2: usize = 24;
const R3: usize = 16;
const R4: usize = 63;

/*
          Round   |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
        ----------+-------------------------------------------------+
         SIGMA[0] |  0  1  2  3  4  5  6  7  8  9 10 11 12 13 14 15 |
         SIGMA[1] | 14 10  4  8  9 15 13  6  1 12  0  2 11  7  5  3 |
         SIGMA[2] | 11  8 12  0  5  2 15 13 10 14  3  6  7  1  9  4 |
         SIGMA[3] |  7  9  3  1 13 12 11 14  2  6  5 10  4  0 15  8 |
         SIGMA[4] |  9  0  5  7  2  4 10 15 14  1 11 12  6  8  3 13 |
         SIGMA[5] |  2 12  6 10  0 11  8  3  4 13  7  5 15 14  1  9 |
         SIGMA[6] | 12  5  1 15 14 13  4 10  0  7  6  3  9  2  8 11 |
         SIGMA[7] | 13 11  7 14 12  1  3  9  5  0 15  4  8  6  2 10 |
         SIGMA[8] |  6 15 14  9 11  3  0  8 12  2 13  7  1  4 10  5 |
         SIGMA[9] | 10  2  8  4  7  6  1  5 15 11  9 14  3 12 13  0 |
        ----------+-------------------------------------------------+
*/

const SIGMA: [[usize; 16]; 12] = [
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
    [11, 8, 12, 0, 5, 2, 15, 13, 10, 14, 3, 6, 7, 1, 9, 4],
    [7, 9, 3, 1, 13, 12, 11, 14, 2, 6, 5, 10, 4, 0, 15, 8],
    [9, 0, 5, 7, 2, 4, 10, 15, 14, 1, 11, 12, 6, 8, 3, 13],
    [2, 12, 6, 10, 0, 11, 8, 3, 4, 13, 7, 5, 15, 14, 1, 9],
    [12, 5, 1, 15, 14, 13, 4, 10, 0, 7, 6, 3, 9, 2, 8, 11],
    [13, 11, 7, 14, 12, 1, 3, 9, 5, 0, 15, 4, 8, 6, 2, 10],
    [6, 15, 14, 9, 11, 3, 0, 8, 12, 2, 13, 7, 1, 4, 10, 5],
    [10, 2, 8, 4, 7, 6, 1, 5, 15, 11, 9, 14, 3, 12, 13, 0],
    [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15],
    [14, 10, 4, 8, 9, 15, 13, 6, 1, 12, 0, 2, 11, 7, 5, 3],
];

/*
3.1.  Mixing Function G
   The G primitive function mixes two input words, "x" and "y", into
   four words indexed by "a", "b", "c", and "d" in the working vector
   v[0..15].  The full modified vector is returned.  The rotation
   constants (R1, R2, R3, R4) are given in Section 2.1.
       FUNCTION G( v[0..15], a, b, c, d, x, y )
       |
       |   v[a] := (v[a] + v[b] + x) mod 2**w
       |   v[d] := (v[d] ^ v[a]) >>> R1
       |   v[c] := (v[c] + v[d])     mod 2**w
       |   v[b] := (v[b] ^ v[c]) >>> R2
       |   v[a] := (v[a] + v[b] + y) mod 2**w
       |   v[d] := (v[d] ^ v[a]) >>> R3
       |   v[c] := (v[c] + v[d])     mod 2**w
       |   v[b] := (v[b] ^ v[c]) >>> R4
       |
       |   RETURN v[0..15]
       |
       END FUNCTION.
*/

fn mixing_g<E: Engine, CS: ConstraintSystem<E>, M>(
    mut cs: M,
    v: &mut [UInt64],
    a: usize,
    b: usize,
    c: usize,
    d: usize,
    x: &UInt64,
    y: &UInt64
) -> Result<(), SynthesisError>
    where M: ConstraintSystem<E, Root=MultiEq<E, CS>>
{
    v[a] = UInt64::addmany(cs.namespace(|| "mixing step 1"), &[v[a].clone(), v[b].clone(), x.clone()])?;
    v[d] = v[d].xor(cs.namespace(|| "mixing step 2"), &v[a])?.rotr(R1);
    v[c] = UInt64::addmany(cs.namespace(|| "mixing step 3"), &[v[c].clone(), v[d].clone()])?;
    v[b] = v[b].xor(cs.namespace(|| "mixing step 4"), &v[c])?.rotr(R2);
    v[a] = UInt64::addmany(cs.namespace(|| "mixing step 5"), &[v[a].clone(), v[b].clone(), y.clone()])?;
    v[d] = v[d].xor(cs.namespace(|| "mixing step 6"), &v[a])?.rotr(R3);
    v[c] = UInt64::addmany(cs.namespace(|| "mixing step 7"), &[v[c].clone(), v[d].clone()])?;
    v[b] = v[b].xor(cs.namespace(|| "mixing step 8"), &v[c])?.rotr(R4);

    Ok(())
}

/*
3.2.  Compression Function F
   Compression function F takes as an argument the state vector "h",
   message block vector "m" (last block is padded with zeros to full
   block size, if required), 2w-bit offset counter "t", and final block
   indicator flag "f".  Local vector v[0..15] is used in processing.  F
   returns a new state vector.  The number of rounds, "r", is 12 for
   BLAKE2b and 10 for BLAKE2s.  Rounds are numbered from 0 to r - 1.
       FUNCTION F( h[0..7], m[0..15], t, f )
       |
       |      // Initialize local work vector v[0..15]
       |      v[0..7] := h[0..7]              // First half from state.
       |      v[8..15] := IV[0..7]            // Second half from IV.
       |
       |      v[12] := v[12] ^ (t mod 2**w)   // Low word of the offset.
       |      v[13] := v[13] ^ (t >> w)       // High word.
       |
       |      IF f = TRUE THEN                // last block flag?
       |      |   v[14] := v[14] ^ 0xFF..FF   // Invert all bits.
       |      END IF.
       |
       |      // Cryptographic mixing
       |      FOR i = 0 TO r - 1 DO           // Ten or twelve rounds.
       |      |
       |      |   // Message word selection permutation for this round.
       |      |   s[0..15] := SIGMA[i mod 10][0..15]
       |      |
       |      |   v := G( v, 0, 4,  8, 12, m[s[ 0]], m[s[ 1]] )
       |      |   v := G( v, 1, 5,  9, 13, m[s[ 2]], m[s[ 3]] )
       |      |   v := G( v, 2, 6, 10, 14, m[s[ 4]], m[s[ 5]] )
       |      |   v := G( v, 3, 7, 11, 15, m[s[ 6]], m[s[ 7]] )
       |      |
       |      |   v := G( v, 0, 5, 10, 15, m[s[ 8]], m[s[ 9]] )
       |      |   v := G( v, 1, 6, 11, 12, m[s[10]], m[s[11]] )
       |      |   v := G( v, 2, 7,  8, 13, m[s[12]], m[s[13]] )
       |      |   v := G( v, 3, 4,  9, 14, m[s[14]], m[s[15]] )
       |      |
       |      END FOR
       |
       |      FOR i = 0 TO 7 DO               // XOR the two halves.
       |      |   h[i] := h[i] ^ v[i] ^ v[i + 8]
       |      END FOR.
       |
       |      RETURN h[0..7]                  // New state.
       |
       END FUNCTION.
*/


fn blake2b_compression<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    h: &mut [UInt64],
    m: &[UInt64],
    t: u128,
    f: bool
) -> Result<(), SynthesisError>
{
    assert_eq!(h.len(), 8);
    assert_eq!(m.len(), 16);

    /*
    static const UInt64_t blake2b_iv[8] =
    {
        0x6A09E667, 0xBB67AE85, 0x3C6EF372, 0xA54FF53A,
        0x510E527F, 0x9B05688C, 0x1F83D9AB, 0x5BE0CD19
    };
    */

    let mut v = Vec::with_capacity(16);
    v.extend_from_slice(h);
    v.push(UInt64::constant(0x6A09E667F3BCC908));
    v.push(UInt64::constant(0xBB67AE8584CAA73B));
    v.push(UInt64::constant(0x3C6EF372FE94F82B));
    v.push(UInt64::constant(0xA54FF53A5F1D36F1));
    v.push(UInt64::constant(0x510E527FADE682D1));
    v.push(UInt64::constant(0x9B05688C2B3E6C1F));
    v.push(UInt64::constant(0x1F83D9ABFB41BD6B));
    v.push(UInt64::constant(0x5BE0CD19137E2179));

    assert_eq!(v.len(), 16);

    v[12] = v[12].xor(cs.namespace(|| "first xor"), &UInt64::constant(t as u64))?;
    v[13] = v[13].xor(cs.namespace(|| "second xor"), &UInt64::constant((t >> 64) as u64))?;

    if f {
        v[14] = v[14].xor(cs.namespace(|| "third xor"), &UInt64::constant(u64::max_value()))?;
    }

    {
        let mut cs = MultiEq::new(&mut cs);

        for i in 0..12 {
            let mut cs = cs.namespace(|| format!("round {}", i));

            let s = SIGMA[i];

            mixing_g(cs.namespace(|| "mixing invocation 1"), &mut v, 0, 4,  8, 12, &m[s[ 0]], &m[s[ 1]])?;
            mixing_g(cs.namespace(|| "mixing invocation 2"), &mut v, 1, 5,  9, 13, &m[s[ 2]], &m[s[ 3]])?;
            mixing_g(cs.namespace(|| "mixing invocation 3"), &mut v, 2, 6, 10, 14, &m[s[ 4]], &m[s[ 5]])?;
            mixing_g(cs.namespace(|| "mixing invocation 4"), &mut v, 3, 7, 11, 15, &m[s[ 6]], &m[s[ 7]])?;

            mixing_g(cs.namespace(|| "mixing invocation 5"), &mut v, 0, 5, 10, 15, &m[s[ 8]], &m[s[ 9]])?;
            mixing_g(cs.namespace(|| "mixing invocation 6"), &mut v, 1, 6, 11, 12, &m[s[10]], &m[s[11]])?;
            mixing_g(cs.namespace(|| "mixing invocation 7"), &mut v, 2, 7,  8, 13, &m[s[12]], &m[s[13]])?;
            mixing_g(cs.namespace(|| "mixing invocation 8"), &mut v, 3, 4,  9, 14, &m[s[14]], &m[s[15]])?;
        }
    }

    for i in 0..8 {
        let mut cs = cs.namespace(|| format!("h[{i}] ^ v[{i}] ^ v[{i} + 8]", i=i));

        h[i] = h[i].xor(cs.namespace(|| "first xor"), &v[i])?;
        h[i] = h[i].xor(cs.namespace(|| "second xor"), &v[i + 8])?;
    }

    Ok(())
}

/*
        FUNCTION BLAKE2( d[0..dd-1], ll, kk, nn )
        |
        |     h[0..7] := IV[0..7]          // Initialization Vector.
        |
        |     // Parameter block p[0]
        |     h[0] := h[0] ^ 0x01010000 ^ (kk << 8) ^ nn
        |
        |     // Process padded key and data blocks
        |     IF dd > 1 THEN
        |     |       FOR i = 0 TO dd - 2 DO
        |     |       |       h := F( h, d[i], (i + 1) * bb, FALSE )
        |     |       END FOR.
        |     END IF.
        |
        |     // Final block.
        |     IF kk = 0 THEN
        |     |       h := F( h, d[dd - 1], ll, TRUE )
        |     ELSE
        |     |       h := F( h, d[dd - 1], ll + bb, TRUE )
        |     END IF.
        |
        |     RETURN first "nn" bytes from little-endian word array h[].
        |
        END FUNCTION.
*/

pub fn blake2b<E: Engine, CS: ConstraintSystem<E>>(
    mut cs: CS,
    input: &[Boolean],
    personalization: &[u8]
) -> Result<Vec<Boolean>, SynthesisError>
{
    use byteorder::{ByteOrder, LittleEndian};

    assert_eq!(personalization.len(), 16);
    assert!(input.len() % 8 == 0);

    let mut h = Vec::with_capacity(8);
    h.push(UInt64::constant(0x6A09E667F3BCC908 ^ 0x01010000 ^ 64));
    h.push(UInt64::constant(0xBB67AE8584CAA73B));
    h.push(UInt64::constant(0x3C6EF372FE94F82B));
    h.push(UInt64::constant(0xA54FF53A5F1D36F1));
    h.push(UInt64::constant(0x510E527FADE682D1));
    h.push(UInt64::constant(0x9B05688C2B3E6C1F));

    // Personalization is stored here
    h.push(UInt64::constant(0x1F83D9ABFB41BD6B ^ LittleEndian::read_u64(&personalization[0..8])));
    h.push(UInt64::constant(0x5BE0CD19137E2179 ^ LittleEndian::read_u64(&personalization[8..16])));

    let mut blocks: Vec<Vec<UInt64>> = vec![];

    for block in input.chunks(1024) {
        let mut this_block = Vec::with_capacity(16);
        for word in block.chunks(64) {
            let mut tmp = word.to_vec();
            while tmp.len() < 64 {
                tmp.push(Boolean::constant(false));
            }
            this_block.push(UInt64::from_bits(&tmp));
        }
        while this_block.len() < 16 {
            this_block.push(UInt64::constant(0));
        }
        blocks.push(this_block);
    }

    if blocks.len() == 0 {
        blocks.push((0..16).map(|_| UInt64::constant(0)).collect());
    }

    for (i, block) in blocks[0..blocks.len() - 1].iter().enumerate() {
        let cs = cs.namespace(|| format!("block {}", i));

        blake2b_compression(cs, &mut h, block, ((i as u128) + 1) * 128, false)?;
    }

    {
        let cs = cs.namespace(|| "final block");

        blake2b_compression(cs, &mut h, &blocks[blocks.len() - 1], (input.len() / 8) as u128, true)?;
    }

    Ok(h.iter().flat_map(|b| b.into_bits()).collect())
}

#[cfg(test)]
mod test {
    use rand::{XorShiftRng, SeedableRng, Rng};
    use bellman::pairing::bls12_381::{Bls12};
    use ::circuit::boolean::{Boolean, AllocatedBit};
    use ::circuit::test::TestConstraintSystem;
    use super::blake2b;
    use bellman::{ConstraintSystem};
    use blake2_rfc::blake2b::Blake2b;

    #[test]
    fn test_blank_hash() {
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let input_bits = vec![];
        let out = blake2b(&mut cs, &input_bits, b"1234567812345678").unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 0);

        // >>> import blake2b from hashlib
        // >>> h = blake2b(digest_size=32, person=b'12345678')
        // >>> h.hexdigest()
        let expected = hex!("8f81e2a7377c3f836c16ff4646bedacfad91eaec3e450b12ac1e9d9b7928dddbebe2f226cc725086d23922a251474a972de855dec7af4d3082d3decdb965166b");

        let mut out = out.into_iter();
        for b in expected.iter() {
            for i in 0..8 {
                let c = out.next().unwrap().get_value().unwrap();

                assert_eq!(c, (b >> i) & 1u8 == 1u8);
            }
        }
    }

    #[test]
    fn test_blake2b_constraints() {
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let input_bits: Vec<_> = (0..1024).map(|i| AllocatedBit::alloc(cs.namespace(|| format!("input bit {}", i)), Some(true)).unwrap().into()).collect();
        blake2b(&mut cs, &input_bits, b"1234567812345678").unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 50880);
    }

    #[test]
    fn test_blake2b_precomp_constraints() {
        // Test that 512 fixed leading bits (constants)
        // doesn't result in more constraints.

        let mut cs = TestConstraintSystem::<Bls12>::new();
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let input_bits: Vec<_> = (0..1024)
          .map(|_| Boolean::constant(rng.gen()))
          .chain((0..1024)
                        .map(|i| AllocatedBit::alloc(cs.namespace(|| format!("input bit {}", i)), Some(true)).unwrap().into()))
          .collect();
        blake2b(&mut cs, &input_bits, b"1234567812345678").unwrap();
        assert!(cs.is_satisfied());
        assert_eq!(cs.num_constraints(), 50880);
    }

    #[test]
    fn test_blake2b_constant_constraints() {
        let mut cs = TestConstraintSystem::<Bls12>::new();
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);
        let input_bits: Vec<_> = (0..1024).map(|_| Boolean::constant(rng.gen())).collect();
        blake2b(&mut cs, &input_bits, b"1234567812345678").unwrap();
        assert_eq!(cs.num_constraints(), 0);
    }

    #[test]
    fn test_blake2b() {
        let mut rng = XorShiftRng::from_seed([0x5dbe6259, 0x8d313d76, 0x3237db17, 0xe5bc0654]);

        for input_len in (0..64).chain((64..256).filter(|a| a % 8 == 0))
        {
            let mut h = Blake2b::with_params(64, &[], &[], b"1234567812345678");

            let data: Vec<u8> = (0..input_len).map(|_| rng.gen()).collect();

            h.update(&data);

            let hash_result = h.finalize();

            let mut cs = TestConstraintSystem::<Bls12>::new();

            let mut input_bits = vec![];

            for (byte_i, input_byte) in data.into_iter().enumerate() {
                for bit_i in 0..8 {
                    let cs = cs.namespace(|| format!("input bit {} {}", byte_i, bit_i));

                    input_bits.push(AllocatedBit::alloc(cs, Some((input_byte >> bit_i) & 1u8 == 1u8)).unwrap().into());
                }
            }

            let r = blake2b(&mut cs, &input_bits, b"1234567812345678").unwrap();

            assert!(cs.is_satisfied());

            let mut s = hash_result.as_ref().iter()
                                            .flat_map(|&byte| (0..8).map(move |i| (byte >> i) & 1u8 == 1u8));

            for b in r {
                match b {
                    Boolean::Is(b) => {
                        assert!(s.next().unwrap() == b.get_value().unwrap());
                    },
                    Boolean::Not(b) => {
                        assert!(s.next().unwrap() != b.get_value().unwrap());
                    },
                    Boolean::Constant(b) => {
                        assert!(input_len == 0);
                        assert!(s.next().unwrap() == b);
                    }
                }
            }
        }
    }
}
