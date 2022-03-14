use crate::Wide;

impl<const N: usize> Wide<N> {
    pub fn shl_with_carry(&self, shift: u32) -> (Self, u64) {
        let n = &self.0;

        let offset = shift as usize / 64;
        let shift = shift % 64;

        if offset >= N {
            panic!("shift left overflow");
        }

        let comp = (64 - shift) % 64;
        let comp_mask = if shift == 0 { 0 } else { !0 };

        let mut r = [0; N];
        let mut carry = 0;

        for i in offset..N {
            let v = n[i - offset];
            r[i] = carry | (v << shift);
            carry = (v >> comp) & comp_mask;
        }

        (Self(r), carry)
    }

    pub fn shr_with_carry(&self, shift: u32) -> (Self, u64) {
        let n = &self.0;

        let offset = shift as usize / 64;
        let shift = shift % 64;

        if offset >= N {
            panic!("shift right overflow");
        }

        let comp = (64 - shift) % 64;
        let comp_mask = if shift == 0 { 0 } else { !0 };

        let mut r = [0; N];
        let mut carry = 0;

        for i in (offset..N).rev() {
            let v = n[i];
            r[i - offset] = carry | (v >> shift);
            carry = (v << comp) & comp_mask;
        }

        (Self(r), carry)
    }
}

impl<const N: usize> std::ops::Shl<u32> for Wide<N> {
    type Output = Self;

    fn shl(self, rhs: u32) -> Self::Output {
        self.shl_with_carry(rhs).0
    }
}

impl<const N: usize> std::ops::Shr<u32> for Wide<N> {
    type Output = Self;

    fn shr(self, rhs: u32) -> Self::Output {
        self.shr_with_carry(rhs).0
    }
}

#[cfg(test)]
mod tests {
    use crate::u256;

    #[test]
    fn shifts_left() {
        let n = u256([0xAAA, 0xBBB, 0xCCC, 0xDDD]) << 60;
        assert_eq!(
            n.0,
            [
                0xA0000000_00000000,
                0xB0000000_000000AA,
                0xC0000000_000000BB,
                0xD0000000_000000CC
            ]
        );
    }

    #[test]
    fn shifts_left_large() {
        let n = u256([0xAAA, 0xBBB, 0xCCC, 0xDDD]) << 188;
        assert_eq!(n.0, [0, 0, 0xA0000000_00000000, 0xB0000000_000000AA]);

        let n = u256([0xAAA, 0xBBB, 0xCCC, 0xDDD]) << 128;
        assert_eq!(n.0, [0, 0, 0xAAA, 0xBBB]);
    }

    #[test]
    fn shifts_left_by_zero() {
        let n = u256([0xAAA, 0xBBB, 0xCCC, 0xDDD]) << 0;
        assert_eq!(n.0, [0xAAA, 0xBBB, 0xCCC, 0xDDD]);
    }

    #[test]
    fn shifts_right() {
        let n = u256([0xAAA, 0xBBB, 0xCCC, 0xDDD]) >> 4;
        assert_eq!(
            n.0,
            [
                0xB0000000_000000AA,
                0xC0000000_000000BB,
                0xD0000000_000000CC,
                0x00000000_000000DD,
            ]
        );
    }

    #[test]
    fn shifts_right_large() {
        let n = u256([0xAAAAAAAA, 0xBBBBBBBB, 0xCCCCCCCC, 0xDDDDDDDD]) >> 144;
        assert_eq!(n.0, [0xDDDD0000_0000CCCC, 0xDDDD, 0, 0]);

        let n = u256([0xA, 0xB, 0xC, 0xD]) >> 128;
        assert_eq!(n.0, [0xC, 0xD, 0, 0]);
    }

    #[test]
    fn shifts_right_by_zero() {
        let n = u256([0xAAA, 0xBBB, 0xCCC, 0xDDD]) >> 0;
        assert_eq!(n.0, [0xAAA, 0xBBB, 0xCCC, 0xDDD]);
    }
}
