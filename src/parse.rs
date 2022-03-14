use super::simd_chunks::{v128, SimdChunk, SimdChunksExt};
use super::u64_ext::{FromStrDecExt, FromStrErr};
use super::{Wide, MAX_WORDS};

const CHUNK_DIGITS: usize = std::mem::size_of::<v128>();
const CHUNK_MULTIPLIER: u64 = 10_u64.pow(CHUNK_DIGITS as u32);

impl<const N: usize> Wide<N> {
    pub fn from_str_dec(src: &str) -> Result<Self, FromStrErr> {
        debug_assert!(N <= MAX_WORDS);

        let src = src.as_bytes();
        if src.is_empty() {
            return Err(FromStrErr::Empty);
        } else if src.len() > 20 * N {
            return Err(FromStrErr::Overflow);
        }

        let mut words = [0_u64; 20 * MAX_WORDS / 16 + 1];
        let mut count = 0;

        let mut chunks = src.simd_rchunks();
        for chunk in &mut chunks {
            words[count] = u64::from_simd_chunk(chunk)?;
            count += 1;
        }

        if let Some(remainder) = chunks.remainder() {
            let len = chunks.remainder_len() as u32;

            words[count] =
                u64::from_simd_chunk(remainder.blend_left_u8(0x30, len))?;
            count += 1;
        }

        let mut r = Self([0; N]);
        r.0[0] = words[count - 1];

        for i in 1..count {
            let (p, mul_overflow) = r.overflowing_mul_word(CHUNK_MULTIPLIER);
            let (s, add_overflow) =
                p.overflowing_add_word(words[count - i - 1]);

            if mul_overflow || add_overflow {
                return Err(FromStrErr::Overflow);
            }

            r = s;
        }

        Ok(r)
    }

    #[cfg(target_feature = "avx2")]
    pub fn from_str_hex(src: &str) -> Result<Self, FromStrErr> {
        debug_assert!(N <= MAX_WORDS);

        use crate::simd_chunks::v256;
        use simd_abstraction::traits::InstructionSet;

        let src = src.as_bytes();
        if src.is_empty() {
            return Err(FromStrErr::Empty);
        } else if src.len() > 16 * N {
            return Err(FromStrErr::Overflow);
        }

        let isa = unsafe { simd_abstraction::arch::x86::AVX2::new_unchecked() };

        let mut r = [0_u64; N];

        let mut chunks = src.simd_rchunks::<v256>();
        let mut i = 0;

        for chunk in &mut chunks {
            if i >= N {
                return Err(FromStrErr::Overflow);
            }

            let decoded =
                simd_abstraction::common::hex::decode_u8x32(isa, chunk)
                    .map_err(|_| FromStrErr::InvalidCharacter)?;

            let swapped = decoded.swap_bytes();

            let mut dst = unsafe {
                std::slice::from_raw_parts_mut(r.as_mut_ptr().add(i).cast(), 16)
            };
            swapped.store_unaligned(&mut dst);
            i += 2;
        }

        if let Some(remainder) = chunks.remainder() {
            if i >= N {
                return Err(FromStrErr::Overflow);
            }

            let padded =
                remainder.blend_left_u8(0x30, chunks.remainder_len() as u32);

            let decoded =
                simd_abstraction::common::hex::decode_u8x32(isa, padded)
                    .map_err(|_| FromStrErr::InvalidCharacter)?;

            let swapped = decoded.swap_bytes();

            let mut dst = unsafe {
                std::slice::from_raw_parts_mut(r.as_mut_ptr().add(i).cast(), 16)
            };
            swapped.store_unaligned(&mut dst);
        }

        Ok(Self(r))
    }
}

impl<const N: usize> std::str::FromStr for Wide<N> {
    type Err = FromStrErr;

    fn from_str(src: &str) -> Result<Self, Self::Err> {
        Self::from_str_dec(src)
    }
}

#[cfg(test)]
mod tests {
    use crate::Wide;
    use quickcheck_macros::quickcheck;

    type U128 = Wide<2>;

    #[test]
    fn parses_basic_numbers() {
        let text = "12345";
        let r = text.parse::<U128>().unwrap();
        assert_eq!(r.0, [12345, 0]);
    }

    #[test]
    fn parses_large_numbers() {
        let text = "12332717382182921391293219327638312835";
        let r = text.parse::<U128>().unwrap();
        assert_eq!(r.0, [5677875087785924483, 668557948920623322]);
    }

    #[test]
    fn parses_hex_numbers() {
        let text = "abcdef123456789aaaaaaaaaa";
        let r = U128::from_str_hex(text).unwrap();
        assert_eq!(r.0, [0x456789aaaaaaaaaa, 0xabcdef123]);
    }

    #[quickcheck]
    fn qc_matches_u128(n: u128) -> bool {
        let p = n.to_string().parse::<U128>();
        p.map_or(false, |parsed| parsed == U128::from_u128(n))
    }
}
