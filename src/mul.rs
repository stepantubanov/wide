use super::Wide;

impl<const N: usize> Wide<N> {
    #[inline]
    pub fn overflowing_mul_word(&self, other: u64) -> (Self, bool) {
        let mut carry = 0;
        let n = self.0;

        let mut r = [0; N];
        for i in 0..N {
            let p = n[i] as u128 * other as u128 + carry as u128;
            r[i] = p as u64;
            carry = (p >> 64) as u64;
        }

        (Self(r), carry != 0)
    }

    pub fn overflowing_mul(&self, other: &Self) -> (Self, bool) {
        // Avoid unnecessary computation if we're not checking
        // overflow.
        const CHECK: bool = crate::overflow::CHECKING_OVERFLOW;

        let n = self.0;
        let m = other.0;

        let mut carry = 0;
        let x = m[0];

        let mut r = [0; N];

        for i in 0..N {
            let p = n[i] as u128 * x as u128 + carry as u128;
            r[i] = p as u64;
            carry = (p >> 64) as u64;
        }

        let mut overflow = carry;

        for j in 1..N {
            carry = 0;
            let x = m[j];

            for i in 0..(N - j) {
                let ri = i + j;

                // Following is always true:
                // (Product of any two u64 + 2*u64::MAX) <= u128::MAX
                // Which means we can safely add in carry without
                // overflowing u128.
                //
                // Example in decimal:
                // Max decimal digit = 9
                // Max decimal two-digit = 99
                // Product (9, 9) = 81
                // 81 + 2*9 <= 99

                let p =
                    n[i] as u128 * x as u128 + r[ri] as u128 + carry as u128;
                carry = (p >> 64) as u64;

                r[ri] = p as u64;
            }

            if CHECK && x != 0 {
                overflow |= carry;

                for i in (N - j)..N {
                    overflow |= n[i];
                }
            }
        }

        (Self(r), CHECK && (overflow != 0))
    }

    #[inline(never)]
    pub fn pow(&self, mut exp: u32) -> Self {
        let mut base = *self;
        let mut result = Self::one();

        while exp != 0 {
            if exp & 1 != 0 {
                result *= base;
            }

            base *= base;
            exp >>= 1;
        }

        result
    }
}

impl<const N: usize> std::ops::Mul<u64> for Wide<N> {
    type Output = Self;

    #[inline]
    fn mul(self, other: u64) -> Self::Output {
        crate::overflow_check! { self.overflowing_mul_word(other) }
    }
}

impl<const N: usize> std::ops::Mul<u64> for &Wide<N> {
    type Output = Wide<N>;

    #[inline]
    fn mul(self, other: u64) -> Self::Output {
        crate::overflow_check! { self.overflowing_mul_word(other) }
    }
}

impl<const N: usize> std::ops::MulAssign<u64> for Wide<N> {
    #[inline]
    fn mul_assign(&mut self, other: u64) {
        *self = crate::overflow_check! { self.overflowing_mul_word(other) };
    }
}

impl<const N: usize> std::ops::Mul<Wide<N>> for Wide<N> {
    type Output = Self;

    #[inline]
    fn mul(self, other: Self) -> Self::Output {
        crate::overflow_check! { self.overflowing_mul(&other) }
    }
}

impl<const N: usize> std::ops::Mul<Wide<N>> for &Wide<N> {
    type Output = Wide<N>;

    #[inline]
    fn mul(self, other: Wide<N>) -> Self::Output {
        crate::overflow_check! { self.overflowing_mul(&other) }
    }
}

impl<const N: usize> std::ops::MulAssign<Wide<N>> for Wide<N> {
    #[inline]
    fn mul_assign(&mut self, other: Self) {
        *self = crate::overflow_check! { self.overflowing_mul(&other) };
    }
}

#[cfg(test)]
mod tests {
    use crate::u256;

    #[test]
    fn mul_word_no_overflow() {
        let n = u256([1 << 35, 1 << 10, 1 << 10, 0]);

        let (r, overflow) = n.overflowing_mul_word((1 << 1) | (1 << 60));
        assert_eq!(r.0, [1 << 36, 1 << 31 | 1 << 11, 1 << 6 | 1 << 11, 1 << 6]);
        assert_eq!(overflow, false);
    }

    #[test]
    fn mul_word_with_overflow() {
        let n = u256([1 << 35, 1 << 10, 1 << 10, 1 << 20]);

        let (r, overflow) = n.overflowing_mul_word((1 << 1) | (1 << 60));
        assert_eq!(
            r.0,
            [
                1 << 36,
                1 << 31 | 1 << 11,
                1 << 6 | 1 << 11,
                1 << 6 | 1 << 21
            ]
        );
        assert_eq!(overflow, true);
    }

    #[test]
    fn mul_no_overflow() {
        // n = 0x100002222222222220000111111111111
        let n = u256([0x1111_1111_1111, 0x2222_2222_2222, 1, 0]);
        // m = 0x1111111111110000000000000001
        let m = u256([1, 0x1111_1111_1111, 0, 0]);

        // p = 0x111113579be0_135797530fedcbaa_89abedcba9876543_0000111111111111
        let (r, overflow) = n.overflowing_mul(&m);
        assert_eq!(
            r.0,
            [
                0x0000111111111111,
                0x89abedcba9876543,
                0x135797530fedcbaa,
                0x0000111113579be0
            ]
        );
        assert_eq!(overflow, false);
    }

    #[test]
    fn mul_with_overflow() {
        let n = u256([u64::MAX, u64::MAX, 0, 0]);
        let m = u256([0, 0, 2, 0]);

        // multiplying by m is equivalent to a bitshift left 129.
        let (r, overflow) = n.overflowing_mul(&m);
        assert_eq!(r.0, [0, 0, u64::MAX << 1, u64::MAX]);
        assert_eq!(overflow, true);
    }

    #[test]
    fn pow() {
        let n = u256::from(123_u64);
        let r = 337587917446653715596592958817679803_u128;
        assert_eq!(n.pow(17), u256::from_u128(r));
    }

    #[test]
    fn implements_operators() {
        let p = u256([1, 2, 3, 4]) * 100;
        assert_eq!(p.0, [100, 200, 300, 400]);

        let p = u256([1, 2, 3, 0]) * u256([5, 10, 0, 0]);
        assert_eq!(p.0, [5, 20, 35, 30]);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "extended arithmetic overflow")]
    fn checks_for_overflow_in_debug() {
        let _ = u256([1, 2, 3, 4]) * u256([5, 10, 15, 20]);
    }
}
