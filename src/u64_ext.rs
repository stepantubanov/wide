use std::arch::x86_64 as arch;
use std::error::Error;
use std::fmt;

use crate::simd_chunks::{v128, SimdChunk, SimdChunksExt};

#[derive(Eq, PartialEq, Debug, Copy, Clone, Hash)]
pub enum FromStrErr {
    Empty,
    InvalidCharacter,
    Overflow,
}

impl fmt::Display for FromStrErr {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let text = match self {
            FromStrErr::Empty => "empty input",
            FromStrErr::InvalidCharacter => "invalid character",
            FromStrErr::Overflow => "overflow",
        };

        f.write_str(text)
    }
}

impl Error for FromStrErr {}

pub trait FromStrDecExt<T: SimdChunk>
where
    Self: Sized,
{
    fn from_str_dec<S: AsRef<[u8]>>(src: S) -> Result<Self, FromStrErr>;
    fn from_simd_chunk(chunk: T) -> Result<Self, FromStrErr>;
}

pub trait ToSimdChunk<T: SimdChunk> {
    fn to_simd_chunk(&self) -> (T, u32);
}

pub struct SimdFormatted(pub u64);

impl fmt::Debug for SimdFormatted {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        <Self as fmt::Display>::fmt(&self, f)
    }
}

impl fmt::Display for SimdFormatted {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        if self.0.leading_zeros() <= 10 {
            // Number is likely longer than 16 digits.
            let hi = self.0 / 10_000;
            let lo = self.0 % 10_000;

            // At most 4 digits (16-bits)
            let n = lo as u32;

            let d100 = n / 100;
            let m100 = n % 100;
            let d0 = d100 / 10;
            let d1 = d100 % 10;
            let d2 = m100 / 10;
            let d3 = m100 % 10;

            let trail = 0x30303030 + (d0 | (d1 << 8) | (d2 << 16) | (d3 << 24));

            let mut bytes = [0; 20];
            let (chunk, offset) = hi.to_simd_chunk();

            // Left-align the chunk.
            let chunk = chunk.rotate(offset);
            chunk.store_unaligned(&mut bytes);

            // FIXME: Store-to-load forwarding...
            unsafe {
                bytes
                    .as_mut_ptr()
                    .add(16 - offset as usize)
                    .cast::<u32>()
                    .write_unaligned(trail);
            }

            f.write_str(unsafe {
                std::str::from_utf8_unchecked(&bytes[..20 - offset as usize])
            })
        } else {
            let mut bytes = [0; 16];
            let (chunk, offset) = self.0.to_simd_chunk();
            chunk.store_unaligned(&mut bytes);

            f.write_str(unsafe {
                std::str::from_utf8_unchecked(&bytes[offset as usize..])
            })
        }
    }
}

impl FromStrDecExt<v128> for u64 {
    fn from_str_dec<S: AsRef<[u8]>>(src: S) -> Result<Self, FromStrErr> {
        let src = src.as_ref();
        if src.len() > 20 {
            return Err(FromStrErr::Overflow);
        }

        let mut chunks = src.simd_rchunks();

        if let Some(chunk) = chunks.next() {
            let result = Self::from_simd_chunk(chunk)?;

            if let Some(remainder) = chunks.remainder_as::<u32>() {
                // Pad remainder in case it's less than 4 digits.
                let rem_bits: usize = 8 * chunks.remainder_len();
                let mask: u32 = ((1 << (32 - rem_bits)) - 1) as u32;
                let remainder = (mask & 0x30303030) | (!mask & remainder);

                // At most 4 bytes left
                let remainder = parse_4_digits(remainder)?;

                // remainder x 10 ** 16
                let remainder = (remainder as u64)
                    .checked_mul(10000000000000000)
                    .ok_or(FromStrErr::Overflow)?;

                let result = result
                    .checked_add(remainder)
                    .ok_or(FromStrErr::Overflow)?;

                Ok(result)
            } else {
                Ok(result)
            }
        } else if let Some(remainder) = chunks.remainder() {
            let len = chunks.remainder_len() as u32;

            Self::from_simd_chunk(remainder.blend_left_u8(0x30, len))
        } else {
            return Err(FromStrErr::Empty);
        }
    }

    #[cfg(target_feature = "sse4.2")]
    fn from_simd_chunk(chunk: v128) -> Result<Self, FromStrErr> {
        unsafe {
            let data = chunk;

            let mul_1_10 = arch::_mm_setr_epi8(
                10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1, 10, 1,
            );
            let mul_1_100 =
                arch::_mm_setr_epi16(100, 1, 100, 1, 100, 1, 100, 1);
            let mul_1_10000 =
                arch::_mm_setr_epi16(10000, 1, 10000, 1, 10000, 1, 10000, 1);

            let data =
                arch::_mm_sub_epi8(data, arch::_mm_set1_epi8(b'0' as i8));

            let check = arch::_mm_cmpgt_epi8(data, arch::_mm_set1_epi8(9));
            let check = arch::_mm_movemask_epi8(check);

            let t1 = arch::_mm_maddubs_epi16(data, mul_1_10);
            let t2 = arch::_mm_madd_epi16(t1, mul_1_100);
            let t3 = arch::_mm_packus_epi32(t2, t2);
            let t4 = arch::_mm_madd_epi16(t3, mul_1_10000);

            let r = arch::_mm_cvtsi128_si64(t4) as u64;

            // TODO: likely/unlikely intrinsics are not working in Rust 1.59.
            // Returning earlier with an Err generates poor assembly (unlikely
            // path is early return of Err).
            if check != 0 {
                Err(FromStrErr::InvalidCharacter)
            } else {
                Ok((r as u32) as u64 * 100000000 + (r >> 32))
            }
        }
    }
}

impl ToSimdChunk<v128> for u64 {
    #[inline]
    fn to_simd_chunk(&self) -> (v128, u32) {
        let hi = self / 100000000;
        let lo = self % 100000000;

        unsafe {
            let x = arch::_mm_set_epi64x(lo as i64, hi as i64);

            // DIV by 10_000 (division via multiplication)
            let div_10000 = arch::_mm_set1_epi32(-776530087);
            let mut x_div_10000 = arch::_mm_mul_epu32(x, div_10000);
            x_div_10000 = arch::_mm_srli_epi64(x_div_10000, 45);

            let mul_10000 = arch::_mm_set1_epi32(10_000);
            let mut x_mod_10000 = arch::_mm_mul_epu32(x_div_10000, mul_10000);
            x_mod_10000 = arch::_mm_sub_epi32(x, x_mod_10000);

            let y = arch::_mm_or_si128(
                x_div_10000,
                arch::_mm_slli_epi64(x_mod_10000, 32),
            );

            // DIV by 100
            let div_100 = arch::_mm_set1_epi16(0x147b);
            let mut y_div_100 = arch::_mm_mulhi_epu16(y, div_100);
            y_div_100 = arch::_mm_srli_epi16(y_div_100, 3);

            let mul_100 = arch::_mm_set1_epi16(100);
            let mut y_mod_100 = arch::_mm_mullo_epi16(y_div_100, mul_100);
            y_mod_100 = arch::_mm_sub_epi16(y, y_mod_100);

            let z = arch::_mm_or_si128(
                y_div_100,
                arch::_mm_slli_epi32(y_mod_100, 16),
            );

            let div_10 = arch::_mm_set1_epi16(0x199a);
            let z_div_10 = arch::_mm_mulhi_epu16(z, div_10);

            let mul_10 = arch::_mm_set1_epi16(10);
            let mut z_mod_10 = arch::_mm_mullo_epi16(z_div_10, mul_10);
            z_mod_10 = arch::_mm_sub_epi16(z, z_mod_10);

            let tmp =
                arch::_mm_or_si128(z_div_10, arch::_mm_slli_epi16(z_mod_10, 8));

            let mask = !arch::_mm_movemask_epi8(arch::_mm_cmpeq_epi8(
                tmp,
                arch::_mm_setzero_si128(),
            ));
            let offset = (mask | 0x8000).trailing_zeros();

            let ascii0 = arch::_mm_set1_epi8(b'0' as i8);
            let digits = arch::_mm_add_epi8(tmp, ascii0);

            (digits, offset)
        }
    }
}

fn parse_4_digits(mut num: u32) -> Result<u32, FromStrErr> {
    num = num.swap_bytes();

    let zero = 0x30303030; // ascii '0'
    num = num.wrapping_sub(zero);

    let mask = 0x80808080; // msb of every byte

    if num & mask != 0 {
        // Symbols below ascii '0'
        return Err(FromStrErr::InvalidCharacter);
    }

    let nine: u32 = 0x09090909;
    let num_inv = nine.wrapping_sub(num);
    if num_inv & mask != 0 {
        // Digits above 9
        return Err(FromStrErr::InvalidCharacter);
    }

    // At this point num = 4 digits

    // Accumulate 2 digits in every other byte.
    num += num * 10 >> 8;

    // Accumulate 4 digits in every other 2-bytes.
    num = (num & 0x00ff00ff).wrapping_mul(100 + (1 << 16)) >> 16;

    Ok(num)
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::simd_chunks::SimdChunk;
    use quickcheck_macros::quickcheck;

    #[test]
    fn parses_small_numbers() {
        assert_eq!(u64::from_str_dec("0"), Ok(0));
        assert_eq!(u64::from_str_dec("9"), Ok(9));
        assert_eq!(u64::from_str_dec("12345"), Ok(12345));
    }

    #[test]
    fn parses_large_numbers() {
        assert_eq!(u64::from_str_dec("1234567890555"), Ok(1234567890555));
        assert_eq!(
            u64::from_str_dec("17876543211234567890"),
            Ok(17876543211234567890)
        );
    }

    #[test]
    fn reports_parsing_errors() {
        assert_eq!(u64::from_str_dec(""), Err(FromStrErr::Empty));
        assert_eq!(u64::from_str_dec("a"), Err(FromStrErr::InvalidCharacter));
        assert_eq!(
            u64::from_str_dec("20000000000000000000"),
            Err(FromStrErr::Overflow)
        );
    }

    #[test]
    fn formats_chunks() {
        let mut buf = [0_u8; 16];

        let n = 1234567890_u64;
        let (chunk, offset) = n.to_simd_chunk();
        chunk.store_unaligned(&mut buf);

        assert_eq!(
            std::str::from_utf8(&buf[offset as usize..]),
            Ok("1234567890")
        );
        assert_eq!(offset, 6);
    }

    #[test]
    fn formats_chunks_with_large_numbers() {
        let mut buf = [0_u8; 16];

        let n = 1234567890123456_u64;
        let (chunk, offset) = n.to_simd_chunk();
        chunk.store_unaligned(&mut buf);

        assert_eq!(
            std::str::from_utf8(&buf[offset as usize..]),
            Ok("1234567890123456")
        );
        assert_eq!(offset, 0);
    }

    #[test]
    fn formats_display() {
        let n = SimdFormatted(123456789);
        assert_eq!(n.to_string(), "123456789");
    }

    #[test]
    fn formats_display_large_numbers() {
        let n = SimdFormatted(12345678901234567890);
        assert_eq!(n.to_string(), "12345678901234567890");

        let n = SimdFormatted(1234567890123456789);
        assert_eq!(n.to_string(), "1234567890123456789");

        let n = SimdFormatted(9_999_999_999_999_999);
        assert_eq!(n.to_string(), "9999999999999999");
    }

    #[quickcheck]
    fn qc_matches_std(n: u64) -> bool {
        u64::from_str_dec(n.to_string()) == Ok(n)
    }
}
