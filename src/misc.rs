use std::cmp::Ordering;

use super::Wide;

macro_rules! impl_bitscan {
    (@forward, $bitscan:ident, $size:tt, $empty:expr) => {
        pub fn $bitscan(&self) -> u32 {
            let n = self.0;

            for i in 0..$size {
                let n = n[i];
                if n != $empty {
                    return (i as u32) * u64::BITS + n.$bitscan();
                }
            }

            Self::BITS
        }
    };
    (@reverse, $bitscan:ident, $size:tt, $empty:expr) => {
        pub fn $bitscan(&self) -> u32 {
            let n = self.0;

            for i in 0..$size {
                let n = n[$size - i - 1];
                if n != $empty {
                    return (i as u32) * u64::BITS + n.$bitscan();
                }
            }

            Self::BITS
        }
    };
}

impl<const N: usize> Wide<N> {
    pub const BITS: u32 = N as u32 * u64::BITS;
    pub const MAX: Self = Self([u64::MAX; N]);
    pub const MIN: Self = Self([0; N]);

    impl_bitscan!(@forward, trailing_zeros, N, 0);
    impl_bitscan!(@forward, trailing_ones, N, u64::MAX);
    impl_bitscan!(@reverse, leading_zeros, N, 0);
    impl_bitscan!(@reverse, leading_ones, N, u64::MAX);

    pub fn leading_bytes(&self) -> u32 {
        self.leading_zeros() / 8
    }

    pub const fn zero() -> Self {
        Self([0; N])
    }

    pub const fn one() -> Self {
        let mut r = [0; N];
        r[0] = 1;
        Self(r)
    }

    pub fn is_zero(&self) -> bool {
        (0..N).all(|i| self.0[i] == 0)
    }

    pub fn count_ones(&self) -> u32 {
        let mut zeros = 0;
        let n = self.0;

        for i in 0..N {
            zeros += n[i].count_ones();
        }

        zeros
    }

    pub fn count_zeros(&self) -> u32 {
        Self::BITS - self.count_ones()
    }

    pub fn is_power_of_two(&self) -> bool {
        // For Intel x86-64 CPUs it'd better to use BLSR.
        // ARM64 and Zen x86-64 are good with pop count.
        self.count_ones() == 1
    }

    pub fn swap_bytes(&self) -> Self {
        let n = self.0;

        let mut r = [0; N];
        for i in 0..N {
            r[i] = n[N - i - 1].swap_bytes();
        }

        Self(r)
    }

    pub fn from_be_bytes(bytes: &[u8]) -> Self {
        // Ensure we have enough input bytes.
        let bytes = &bytes[..N * 8];

        let mut r = [0; N];
        for i in 0..N {
            let offset = (N - i - 1) * 8;

            // SAFETY: Checked number of bytes at function entry.
            let bytes: [u8; 8] = unsafe {
                bytes[offset..offset + 8].try_into().unwrap_unchecked()
            };
            r[i] = u64::from_be_bytes(bytes);
        }

        Self(r)
    }

    pub fn from_le_bytes(bytes: &[u8]) -> Self {
        // Ensure we have enough input bytes.
        let bytes = &bytes[..N * 8];

        let mut r = [0; N];
        for i in 0..N {
            let offset = i * 8;

            // SAFETY: Checked number of bytes at function entry.
            let bytes: [u8; 8] = unsafe {
                bytes[offset..offset + 8].try_into().unwrap_unchecked()
            };
            r[i] = u64::from_le_bytes(bytes);
        }

        Self(r)
    }

    pub fn write_be_bytes(&self, buf: &mut [u8]) {
        // Ensure we have enough output bytes.
        let _ = &buf[..N * 8];

        let n = self.0;
        for i in 0..N {
            let offset = (N - 1 - i) * 8;
            let dst: &mut [u8; 8] =
                (&mut buf[offset..offset + 8]).try_into().unwrap();

            *dst = n[i].to_be_bytes();
        }
    }

    #[inline]
    pub fn from_u128(n: u128) -> Self {
        let mut r = [0; N];
        r[0] = n as u64;
        r[1] = (n >> 64) as u64;

        Self(r)
    }
}

impl<const N: usize> From<u64> for Wide<N> {
    #[inline]
    fn from(n: u64) -> Self {
        let mut r = [0; N];
        r[0] = n;

        Self(r)
    }
}

impl<const N: usize> Default for Wide<N> {
    #[inline]
    fn default() -> Self {
        Self([0; N])
    }
}

fn compare<const N: usize>(a: &Wide<N>, b: &Wide<N>) -> Ordering {
    let a = a.0;
    let b = b.0;

    for i in (0..N).rev() {
        if a[i] < b[i] {
            return Ordering::Less;
        } else if a[i] > b[i] {
            return Ordering::Greater;
        }
    }

    Ordering::Equal
}

impl<const N: usize> std::cmp::PartialOrd for Wide<N> {
    fn partial_cmp(&self, other: &Self) -> Option<Ordering> {
        Some(compare(&self, other))
    }
}

impl<const N: usize> std::cmp::Ord for Wide<N> {
    fn cmp(&self, other: &Self) -> Ordering {
        compare(&self, other)
    }
}

#[cfg(test)]
mod tests {
    use std::cmp::Ordering;

    use crate::u256;

    #[test]
    fn counts_leading_zeros() {
        let n = u256([u64::MAX, u64::MAX, 1 << 1, 0]);
        assert_eq!(n.leading_zeros(), 64 + 62);

        assert_eq!(u256::MIN.leading_zeros(), 256);
    }

    #[test]
    fn counts_leading_ones() {
        let n = u256([u64::MAX, u64::MAX ^ (1 << 5), u64::MAX, u64::MAX]);
        assert_eq!(n.leading_ones(), 64 * 3 - 6);

        assert_eq!(u256::MAX.leading_ones(), 256);
    }

    #[test]
    fn counts_trailing_zeros() {
        let n = u256([0, 1 << 3, 0, 0]);
        assert_eq!(n.trailing_zeros(), 64 + 3);
    }

    #[test]
    fn counts_trailing_ones() {
        let n = u256([u64::MAX, u64::MAX ^ (1 << 12), 0, 0]);
        assert_eq!(n.trailing_ones(), 64 + 12);
    }

    #[test]
    fn counts_ones() {
        let n = u256([u64::MAX, u64::MAX ^ (1 << 5), u64::MAX, u64::MAX]);
        assert_eq!(n.count_ones(), 255);
    }

    #[test]
    fn count_zeros() {
        let n = u256([u64::MAX, u64::MAX ^ (1 << 5), u64::MAX, u64::MAX]);
        assert_eq!(n.count_zeros(), 1);
    }

    #[test]
    fn checks_power_of_two() {
        let n = u256([0, 128, 0, 0]);
        assert_eq!(n.is_power_of_two(), true);

        let n = u256([2, 8, 0, 0]);
        assert_eq!(n.is_power_of_two(), false);

        let n = u256([0, 0, 0, 0]);
        assert_eq!(n.is_power_of_two(), false);
    }

    #[test]
    fn swaps_bytes() {
        let n = u256([0x11223344_55667788, 1, 2, 0xAABBCCDD_EEFFDDCC]);
        let swapped = n.swap_bytes();
        assert_eq!(
            swapped.0,
            [0xCCDDFFEE_DDCCBBAA, 2 << 56, 1 << 56, 0x88776655_44332211]
        );
    }

    #[test]
    fn from_be_bytes() {
        let bytes: [u8; 32] = (0..32).collect::<Vec<_>>().try_into().unwrap();
        let n = u256::from_be_bytes(&bytes).0;

        assert_eq!(n[0], 0x18191a1b_1c1d1e1f);
        assert_eq!(n[1], 0x10111213_14151617);
        assert_eq!(n[2], 0x08090a0b_0c0d0e0f);
        assert_eq!(n[3], 0x00010203_04050607);
    }

    #[test]
    fn from_le_bytes() {
        let bytes: [u8; 32] = (0..32).collect::<Vec<_>>().try_into().unwrap();
        let n = u256::from_le_bytes(&bytes).0;

        assert_eq!(n[0], 0x07060504_03020100);
        assert_eq!(n[1], 0x0f0e0d0c_0b0a0908);
        assert_eq!(n[2], 0x17161514_13121110);
        assert_eq!(n[3], 0x1f1e1d1c_1b1a1918);
    }

    #[test]
    fn compares() {
        let a = u256([0, 1, 2, 3]);
        let b = u256([0, 1, 2, 4]);
        let c = u256([1, 1, 2, 4]);
        let d = u256([1, 2, 5, 2]);

        assert_eq!(a.cmp(&b), Ordering::Less);
        assert_eq!(b.cmp(&c), Ordering::Less);
        assert_eq!(c.cmp(&d), Ordering::Greater);
        assert_eq!(d.cmp(&d), Ordering::Equal);
    }
}
