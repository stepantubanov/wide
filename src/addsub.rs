use super::Wide;

impl<const N: usize> Wide<N> {
    #[inline]
    pub fn overflowing_add_word(&self, other: u64) -> (Self, bool) {
        let mut r = *&self.0;

        let mut carry;

        // Using u128 seems to generate better asm than
        // u64::overflowing_add.

        let sum = r[0] as u128 + other as u128;
        r[0] = sum as u64;
        carry = (sum >> 64) as u64;

        for i in 1..N {
            let sum = r[i] as u128 + carry as u128;
            r[i] = sum as u64;
            carry = (sum >> 64) as u64;
        }

        (Self(r), carry != 0)
    }

    #[inline]
    pub fn overflowing_add(&self, other: &Self) -> (Self, bool) {
        let lhs = self.0;
        let rhs = other.0;

        let mut carry = 0;

        let mut r = [0; N];
        for i in 0..N {
            let sum = lhs[i] as u128 + rhs[i] as u128 + carry as u128;

            r[i] = sum as u64;
            carry = (sum >> 64) as u64;
        }

        (Self(r), carry != 0)
    }

    #[inline]
    pub fn borrowing_sub(&self, other: &Self) -> (Self, bool) {
        let lhs = self.0;
        let rhs = other.0;

        let mut borrow = 0;

        let mut r = [0; N];
        for i in 0..N {
            let diff = (lhs[i] as u128)
                .wrapping_sub(rhs[i] as u128)
                .wrapping_sub(borrow as u128);

            r[i] = diff as u64;
            borrow = (diff >> 127) as u64;
        }

        (Self(r), borrow != 0)
    }
}

impl<const N: usize> std::ops::Add<Wide<N>> for Wide<N> {
    type Output = Self;

    #[inline]
    fn add(self, other: Self) -> Self::Output {
        crate::overflow_check! { self.overflowing_add(&other) }
    }
}

impl<const N: usize> std::ops::Add<u64> for Wide<N> {
    type Output = Self;

    #[inline]
    fn add(self, other: u64) -> Self::Output {
        crate::overflow_check! { self.overflowing_add_word(other) }
    }
}

impl<const N: usize> std::ops::Sub<Wide<N>> for Wide<N> {
    type Output = Self;

    #[inline]
    fn sub(self, other: Self) -> Self::Output {
        crate::overflow_check! { self.borrowing_sub(&other) }
    }
}

#[cfg(test)]
mod tests {
    use crate::u256;
    use quickcheck_macros::quickcheck;

    #[test]
    fn add_word() {
        let (sum, overflow) =
            u256([u64::MAX, 1, 2, 3]).overflowing_add_word(1000);
        assert_eq!(sum.0, [999, 2, 2, 3]);
        assert_eq!(overflow, false);

        let (sum, overflow) = u256([u64::MAX, u64::MAX, u64::MAX, u64::MAX])
            .overflowing_add_word(1);
        assert_eq!(sum.0, [0, 0, 0, 0]);
        assert_eq!(overflow, true);
    }

    #[test]
    fn add_without_overflow() {
        let (sum, overflow) = u256([u64::MAX, u64::MAX, u64::MAX, 16])
            .overflowing_add(&u256([0, 1, 2, 3]));
        assert_eq!(sum.0, [u64::MAX, 0, 2, 20]);
        assert_eq!(overflow, false);
    }

    #[test]
    fn add_with_overflow() {
        let (sum, overflow) = u256([2, 4, u64::MAX, u64::MAX])
            .overflowing_add(&u256([1, 1, 1, 0]));
        assert_eq!(sum.0, [3, 5, 0, 0]);
        assert_eq!(overflow, true);
    }

    #[test]
    fn sub_without_overflow() {
        let (diff, overflow) =
            u256([0, 1, 2, 0]).borrowing_sub(&u256([1, 2, 1, 0]));
        assert_eq!(diff.0, [u64::MAX, u64::MAX - 1, 0, 0]);
        assert_eq!(overflow, false);
    }

    #[test]
    fn sub_with_overflow() {
        let (diff, overflow) =
            u256([0, 1, 2, 3]).borrowing_sub(&u256([0, 1, 3, 4]));
        assert_eq!(diff.0, [0, 0, u64::MAX, u64::MAX - 1]);
        assert_eq!(overflow, true);
    }

    #[test]
    fn implements_operators() {
        let sum = u256([9, 8, 7, 6]) + u256([1, 2, 3, 4]);
        assert_eq!(sum.0, [10, 10, 10, 10]);
    }

    #[cfg(debug_assertions)]
    #[test]
    #[should_panic(expected = "extended arithmetic overflow")]
    fn checks_for_overflow_in_debug() {
        let _ = u256([9, 8, 7, 6]) - u256([0, 0, 0, 7]);
    }

    #[quickcheck]
    fn qc_sub_from_sum(a: u256, b: u256) -> bool {
        let (sum, ov) = a.overflowing_add(&b);
        let (sub, br) = sum.borrowing_sub(&a);

        sub == b && ov == br
    }
}
