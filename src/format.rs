use std::fmt;

use crate::simd_chunks::SimdChunk;

use super::u64_ext::ToSimdChunk;
use super::{Wide, MAX_WORDS};

#[inline(always)]
fn mulhi(n: u128, c: u128) -> u128 {
    let n0 = n as u64;
    let n1 = (n >> 64) as u64;

    let c0 = c as u64;
    let c1 = (c >> 64) as u64;

    let r00 = n0 as u128 * c0 as u128;
    let r01 = n0 as u128 * c1 as u128 + (r00 >> 64);

    let r11 = n1 as u128 * c0 as u128 + (r01 as u64) as u128;
    let r12 = n1 as u128 * c1 as u128 + (r11 >> 64) + (r01 >> 64);

    r12
}

#[inline(always)]
fn divmod_1e16(n: u128) -> (u128, u64) {
    const C: u128 = 306499108173177771671669405430061836724;

    let q = mulhi(n, C) >> (181 - 128);
    let r = n - q * 1e16 as u128;

    (q, r as u64)
}

fn wide_divmod_1e16<const N: usize>(w: &Wide<N>) -> (Wide<N>, u64) {
    let n = w.0;

    let mut q = [0; N];

    q[N - 1] = n[N - 1] / 1e16 as u64;
    let mut r = n[N - 1] % 1e16 as u64;

    for i in 1..N {
        let num = (r as u128) << 64 | (n[N - i - 1] as u128);

        let (qi, ri) = divmod_1e16(num);
        q[N - i - 1] = qi as u64;
        r = ri;
    }

    (Wide(q), r)
}

impl<const N: usize> fmt::Display for Wide<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        let (mut q, mut r) = wide_divmod_1e16(&self);

        let mut buf = [0; MAX_WORDS * 20];
        let mut offset = MAX_WORDS * 20 - 16;

        loop {
            let (chunk, chunk_offset) = r.to_simd_chunk();

            chunk.store_unaligned(&mut buf[offset..]);

            if q.is_zero() {
                offset += chunk_offset as usize;
                break;
            }

            (q, r) = wide_divmod_1e16(&q);
            offset -= 16;
        }

        f.write_str(unsafe { std::str::from_utf8_unchecked(&buf[offset..]) })
    }
}

impl<const N: usize> fmt::Debug for Wide<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        f.write_str("Wide(")?;
        <Self as fmt::Display>::fmt(&self, f)?;
        f.write_str(")")
    }
}

impl<const N: usize> fmt::LowerHex for Wide<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        format_hex(&self, f, hex_simd::AsciiCase::Lower)
    }
}

impl<const N: usize> fmt::UpperHex for Wide<N> {
    fn fmt(&self, f: &mut fmt::Formatter) -> fmt::Result {
        format_hex(&self, f, hex_simd::AsciiCase::Upper)
    }
}

fn format_hex<const N: usize>(
    src: &Wide<N>,
    f: &mut fmt::Formatter,
    case: hex_simd::AsciiCase,
) -> fmt::Result {
    let zero_digits = std::cmp::min(src.leading_zeros() / 4, N as u32 * 16 - 1);
    let swapped = src.swap_bytes();

    let src: &[u8] =
        unsafe { std::slice::from_raw_parts(swapped.0.as_ptr().cast(), 8 * N) };

    let mut buf = [0; MAX_WORDS * 16];
    let buf =
        hex_simd::encode(src, hex_simd::OutBuf::from_slice_mut(&mut buf), case)
            .expect("hex encode failed");

    let encoded =
        unsafe { std::str::from_utf8_unchecked(&buf[zero_digits as usize..]) };

    f.write_str(encoded)
}

#[cfg(test)]
mod tests {
    use crate::Wide;
    use quickcheck_macros::quickcheck;

    #[test]
    fn formats_numbers() {
        let w = Wide::<2>([5677875087785924483, 668557948920623322]);
        let expected = "12332717382182921391293219327638312835";
        let formatted = format!("{w}");
        assert_eq!(formatted, expected);
    }

    #[test]
    fn formats_lower_hex() {
        let w = Wide::<2>([0x12345678901, 0xaaaabbbbccccdddd]);
        let expected = "aaaabbbbccccdddd0000012345678901";
        let formatted = format!("{:x}", w);
        assert_eq!(formatted, expected);
    }

    #[test]
    fn formats_upper_hex() {
        let w = Wide::<2>([0x12345, 0xABCDE]);
        let expected = "ABCDE0000000000012345";
        let formatted = format!("{:X}", w);
        assert_eq!(formatted, expected);
    }

    #[test]
    fn formats_hex_zero() {
        let w = Wide::<2>([0, 0]);
        let expected = "0";
        let formatted = format!("{:x}", w);
        assert_eq!(formatted, expected);
    }

    #[quickcheck]
    fn qc_matches_u128(n: u128) -> bool {
        let w = Wide::<2>::from_u128(n);
        n.to_string() == w.to_string()
    }
}
