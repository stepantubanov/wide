use crate::MAX_WORDS;

use super::Wide;

const fn recip_table() -> [u16; 256] {
    let mut table = [0; 256];
    let mut i = 0;

    while i < 256 {
        // (2**19 - 3*2**8) / d9
        table[i] = ((0x80000 - 0x300) / (i + 256)) as u16;
        i += 1;
    }

    table
}

const RECIP_TABLE: [u16; 256] = recip_table();

#[inline(always)]
fn reciprocal(d: u64) -> u64 {
    use std::num::Wrapping as W;

    debug_assert!(d >> 63 != 0);

    let v0 = W(RECIP_TABLE[(d >> 55) as usize - 256] as u32);
    let d40 = W((d >> 24) + 1);
    let d0 = W(d & 1);
    let d63 = W(d >> 1) + d0;
    let v1 =
        W((v0.0 << 11) as u64) - (d40 * W((v0 * v0).0 as u64) >> 40) - W(1);

    let v2 = (v1 << 13) + (v1 * (W(1_u64 << 60) - v1 * d40) >> 47);

    // multiplication by d0 is replaced by bitwise and because
    // d0 is a single bit (value: 0 or 1).
    let e = ((v2 >> 1) & (!d0 + W(1))) - v2 * d63;

    let v3 = W((W(v2.0 as u128 * e.0 as u128) >> 65).0 as u64) + (v2 << 31);

    let v4 = v3
        - W(((W(v3.0 as u128 * d as u128) + W(d as u128)) >> 64).0 as u64)
        - W(d);

    v4.0
}

#[inline(always)]
fn divmod(u: u128, d: u64, v: u64) -> (u64, u64) {
    use std::num::Wrapping as W;

    debug_assert!(((u >> 64) as u64) < d);
    debug_assert!((d >> 63) != 0);

    let q = W((u >> 64) * v as u128) + W(u);
    let mut q1 = W((q.0 >> 64) as u64) + W(1);

    let d = W(d);
    let mut r = W(u as u64) - q1 * d;

    let mask0 = if r > W(q.0 as u64) { W(!0) } else { W(0) };
    q1 += mask0;
    r += d & mask0;

    let mask1 = if r >= d { W(!0) } else { W(0) };
    q1 -= mask1;
    r -= d & mask1;

    (q1.0, r.0)
}

#[inline(always)]
fn shl_inplace<const N: usize>(n: &mut [u64; MAX_WORDS], shift: u32) -> usize {
    let comp = (64 - shift) % 64;
    let comp_mask = if shift == 0 { 0 } else { !0 };

    let mut carry = 0;
    let mut zeros = 0;

    for i in 0..N {
        let v = n[i];
        n[i] = carry | (v << shift);
        carry = (v >> comp) & comp_mask;

        zeros = if n[i] != 0 { 0 } else { zeros + 1 };
    }

    n[N] = carry;
    zeros = if carry != 0 { 0 } else { zeros + 1 };

    N + 1 - zeros
}

#[inline(always)]
fn shr_inplace<const N: usize>(n: &mut [u64; MAX_WORDS], shift: u32) {
    let comp = (64 - shift) % 64;
    let comp_mask = if shift == 0 { 0 } else { !0 };

    let mut carry = 0;

    for i in (0..N).rev() {
        let v = n[i];
        n[i] = carry | (v >> shift);
        carry = (v << comp) & comp_mask;
    }
}

#[inline(always)]
fn add_inplace<'a, const N: usize>(
    u: &mut NumeratorChunk<'a, N>,
    d: &[u64; N],
) {
    let mut carry = 0;

    for i in 0..N {
        let sum = d[i] as u128 + u[i] as u128 + carry as u128;
        u[i] = sum as u64;
        carry = (sum >> 64) as u64;
    }

    u[N] = u[N].wrapping_add(carry);
}

#[inline(always)]
fn submul_inplace<'a, const N: usize>(
    u: &mut NumeratorChunk<'a, N>,
    d: &[u64; N],
    q: u64,
) -> bool {
    let mut carry = 0;
    let mut borrow = 0;

    for i in 0..N {
        let p = q as u128 * d[i] as u128 + carry as u128;
        carry = (p >> 64) as u64;

        let diff = (u[i] as u128)
            .wrapping_sub(p as u64 as u128)
            .wrapping_sub(borrow as u128);

        u[i] = diff as u64;
        borrow = (diff >> 127) as u64;
    }

    let diff = (u[N] as u128)
        .wrapping_sub(carry as u128)
        .wrapping_sub(borrow as u128);

    u[N] = diff as u64;
    borrow = (diff >> 127) as u64;

    borrow != 0
}

struct Numerator<const N: usize> {
    u: [u64; MAX_WORDS],
}

impl<const N: usize> Numerator<N> {
    fn new(u: &[u64; N]) -> Self {
        let mut numerator = Numerator { u: [0; MAX_WORDS] };

        // SAFETY:
        // MAX_WORS >= N.
        unsafe {
            let ptr = numerator.u.as_mut_ptr() as *mut [u64; N];
            *ptr = *u;
        }

        numerator
    }

    fn as_chunks<'a>(
        &'a mut self,
        u_len: usize,
        d_len: usize,
    ) -> NumeratorChunks<'a, N> {
        NumeratorChunks {
            inner: self,
            m: u_len - d_len,
        }
    }

    fn as_mut(&mut self) -> &mut [u64; MAX_WORDS] {
        &mut self.u
    }

    fn as_array(&self) -> &[u64; N] {
        // SAFETY:
        // MAX_WORDS >= N and we're explicitly selecting N items here.
        unsafe { self.u[..N].try_into().unwrap_unchecked() }
    }
}

struct NumeratorChunk<'a, const N: usize> {
    u: *mut u64,
    _marker: std::marker::PhantomData<&'a u64>,
}

impl<'a, const N: usize> std::ops::Index<usize> for NumeratorChunk<'a, N> {
    type Output = u64;

    fn index(&self, index: usize) -> &Self::Output {
        if index <= N {
            unsafe { &*self.u.add(index) }
        } else {
            panic!("numerator access out of bounds");
        }
    }
}

impl<'a, const N: usize> std::ops::IndexMut<usize> for NumeratorChunk<'a, N> {
    fn index_mut(&mut self, index: usize) -> &mut Self::Output {
        if index <= N {
            unsafe { &mut *self.u.add(index) }
        } else {
            panic!("numerator access out of bounds");
        }
    }
}

struct NumeratorChunks<'a, const N: usize> {
    inner: &'a mut Numerator<N>,
    m: usize,
}

impl<'a, const N: usize> Iterator for NumeratorChunks<'a, N> {
    type Item = (usize, NumeratorChunk<'a, N>);

    fn next(&mut self) -> Option<Self::Item> {
        if self.m == 0 {
            return None;
        }

        self.m -= 1;

        Some((
            self.m,
            NumeratorChunk {
                u: unsafe { self.inner.u.as_mut_ptr().add(self.m) },
                _marker: Default::default(),
            },
        ))
    }
}

#[derive(Copy, Clone, Debug)]
pub struct Divisor<T> {
    pub d_norm: T,
    pub recip: u64,
    pub norm: u32,
    pub words: u32,
}

impl From<u64> for Divisor<u64> {
    fn from(d: u64) -> Self {
        let norm = d.leading_zeros();
        let d_norm = d << norm;

        Divisor {
            d_norm,
            recip: reciprocal(d_norm),
            norm,
            words: 1,
        }
    }
}

impl<const N: usize> From<Wide<N>> for Divisor<Wide<N>> {
    fn from(d: Wide<N>) -> Self {
        let norm = d.leading_zeros();
        if norm == N as u32 * 64 {
            panic!("division by zero");
        }

        let words = N as u32 - (norm / 64);
        let norm = norm % 64;
        let d_norm = d << norm;

        Divisor {
            d_norm,
            recip: reciprocal(d_norm.0[words as usize - 1]),
            norm,
            words,
        }
    }
}

impl<const N: usize> Wide<N> {
    pub fn div_mod_word(&self, divisor: &Divisor<u64>) -> (Self, u64) {
        let &Divisor {
            d_norm,
            recip,
            norm,
            words: _,
        } = divisor;

        let (mut u, mut carry) = self.shl_with_carry(norm);

        for i in (0..N).rev() {
            let t = ((carry as u128) << 64) | (u.0[i] as u128);
            let (q, r) = divmod(t, d_norm, recip);

            u.0[i] = q;
            carry = r;
        }

        (u, carry >> norm)
    }

    pub fn div_mod(&self, divisor: &Divisor<Wide<N>>) -> (Self, Self) {
        let &Divisor {
            d_norm,
            recip,
            norm,
            words,
        } = divisor;

        if words == 1 {
            let (q, r) = self.div_mod_word(&Divisor {
                d_norm: d_norm.0[0],
                recip,
                norm,
                words,
            });

            return (q, Self::from(r));
        }

        // Normalize numerator

        let mut numerator = Numerator::new(&self.0);

        let u_len = shl_inplace::<N>(numerator.as_mut(), norm);
        let d_len = words as usize;

        if u_len < d_len {
            return (Self::zero(), *self);
        }

        let den = d_norm.0[d_len - 1];
        let den_next = d_norm.0[d_len - 2];

        let u_len = if numerator.u[u_len - 1] >= den {
            u_len + 1
        } else {
            u_len
        };

        // Compute.
        // Note that this loop is not entered if d_len == u_len
        // in which case the result of the divmod is q = 0 and r = u.

        let mut q = [0; N];
        let chunk_len = d_len + 1;

        //for j in (d_len..u_len).rev() {
        for (i, mut u) in numerator.as_chunks(u_len, d_len) {
            // Estimate current quotient.
            // This will always be either exact quotient or in a very unlikely
            // case an over-estimation by 1.
            let mut qh = {
                let (qh, rh) = divmod(
                    ((u[chunk_len - 1] as u128) << 64)
                        | (u[chunk_len - 2] as u128),
                    den,
                    recip,
                );

                let p_next = (den_next as u128) * (qh as u128);

                if p_next > ((rh as u128) << 64) | (u[chunk_len - 3] as u128) {
                    qh - 1
                } else {
                    qh
                }
            };

            // u -= qh * d
            let borrow = submul_inplace(&mut u, &d_norm.0, qh);
            if borrow {
                // This should be VERY UNLIKELY.
                // Add it back.
                qh -= 1;
                add_inplace(&mut u, &d_norm.0);
            }

            q[i] = qh;
        }

        shr_inplace::<N>(numerator.as_mut(), norm);

        (Self(q), Self(*numerator.as_array()))
    }
}

impl<const N: usize> std::ops::Div<u64> for Wide<N> {
    type Output = Self;

    #[inline]
    fn div(self, other: u64) -> Self::Output {
        self.div_mod_word(&Divisor::from(other)).0
    }
}

impl<const N: usize> std::ops::Div<u64> for &Wide<N> {
    type Output = Wide<N>;

    #[inline]
    fn div(self, other: u64) -> Self::Output {
        self.div_mod_word(&Divisor::from(other)).0
    }
}

impl<const N: usize> std::ops::Rem<u64> for Wide<N> {
    type Output = u64;

    #[inline]
    fn rem(self, other: u64) -> u64 {
        self.div_mod_word(&Divisor::from(other)).1
    }
}

impl<const N: usize> std::ops::Rem<u64> for &Wide<N> {
    type Output = u64;

    #[inline]
    fn rem(self, other: u64) -> u64 {
        self.div_mod_word(&Divisor::from(other)).1
    }
}

impl<const N: usize> std::ops::Div<Wide<N>> for Wide<N> {
    type Output = Self;

    #[inline]
    fn div(self, other: Self) -> Self::Output {
        self.div_mod(&Divisor::from(other)).0
    }
}

#[cfg(test)]
mod tests {
    use crate::{rng, u256};
    use quickcheck::TestResult;
    use quickcheck_macros::quickcheck;
    use rand::Rng;

    use super::*;

    #[test]
    fn div_word() {
        let n = u256([1, 2, 3, 4]);
        let q = n / 55;
        assert_eq!(
            q.0,
            [
                9726465057046854488,
                4024744161536629443,
                1341581387178876481,
                0
            ]
        );
    }

    #[test]
    fn rem_word() {
        let n = u256([1, 2, 3, 4]);
        let q = n % 55;
        assert_eq!(q, 25);
    }

    #[test]
    fn div_max() {
        let n = u256([u64::MAX, u64::MAX, u64::MAX, u64::MAX]);
        let d = u64::MAX;

        let (q, r) = n.div_mod_word(&Divisor::from(d));
        let e = q * d + r;
        assert_eq!(e, n);
    }

    #[test]
    fn div_long_basic() {
        let n = u256::from_str_dec(
            "93380292152458389676190732031659723404631639737317947099205327986273563767766"
        ).unwrap();

        let d = u256::from_str_dec(
            "26968136159595354887625979741060229206366361735379159842243182716404241106019"
        ).unwrap();

        let (q, r) = n.div_mod(&Divisor::from(d));

        assert_eq!(q * d + r, n);
    }

    #[test]
    fn div_long_same_size_but_smaller() {
        let n = u256([105, 6, 0, 0]);
        let d = u256([1, 7, 0, 0]);

        let (q, r) = n.div_mod(&Divisor::from(d));
        assert_eq!(q, u256::zero());
        assert_eq!(r, n);
    }

    #[test]
    fn div_long_special() {
        let cases = [
            (
                // This is where q-hat is an over-estimation and is corrected
                // cheaply by the "next product" heuristic.
                u256([0, 0, u64::MAX << 1, 1]),
                u256([0, u64::MAX, u64::MAX, 0]),
            ),
            (
                // This touches on the add-back code that is unlikely to happen
                // in random or usual production data.
                u256([0, 0, 1, u64::MAX / 2 - 1]),
                u256([u64::MAX, u64::MAX, u64::MAX / 2 + 1, 0]),
            ),
            (
                // Just seeing if anything overflows
                u256([!0, !0, !0, !0]),
                u256([!0, !0, !0, !0]),
            ),
        ];

        for (n, d) in cases {
            let (q, r) = n.div_mod(&Divisor::from(d));
            assert_eq!(q * d + r, n);
        }
    }

    #[test]
    fn long_spotcheck() {
        let mut rng = rng();

        for _ in 0..100 {
            let mut n = [0; 4];
            let mut d = [0; 4];

            let num_len = 1 + rng.gen::<usize>() % 3;
            let den_len = 1 + rng.gen::<usize>() % 3;

            for i in 0..num_len {
                n[i] = rng.gen::<u64>();
            }
            for i in 0..den_len {
                d[i] = rng.gen::<u64>();
            }

            let n = u256(n);
            let d = u256(d);

            if d.is_zero() {
                break;
            }

            let (q, r) = n.div_mod(&Divisor::from(d));

            assert_eq!(q * d + r, n, "div failed for n={n}, d={d}");
        }
    }

    #[quickcheck]
    fn qc_reconstructible_single(n: u256, d: u64) -> TestResult {
        if d == 0 {
            return TestResult::discard();
        }

        let (q, r) = n.div_mod_word(&Divisor::from(d));
        let e = q * d + r;
        TestResult::from_bool(e == n)
    }
}
