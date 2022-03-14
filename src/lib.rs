mod addsub;
mod bits;
mod div;
mod format;
mod misc;
mod mul;
pub mod overflow;
mod parse;
pub mod simd_chunks;
pub mod u64_ext;

pub use div::Divisor;

pub const MAX_WORDS: usize = 8;

#[derive(Eq, PartialEq, Hash, Copy, Clone)]
pub struct Wide<const N: usize>(pub [u64; N]);

#[allow(non_camel_case_types)]
pub type u256 = Wide<4>;
pub fn u256(n: [u64; 4]) -> u256 {
    Wide(n)
}

#[cfg(test)]
impl<const N: usize> Arbitrary for Wide<N> {
    fn arbitrary(g: &mut quickcheck::Gen) -> Self {
        let mut r = [0_u64; N];
        for i in 0..N {
            r[i] = u64::arbitrary(g);
        }
        Self(r)
    }
}

#[macro_use]
mod unroll;

#[cfg(test)]
use quickcheck::Arbitrary;

#[cfg(test)]
pub fn rng() -> rand_pcg::Pcg64 {
    let now = std::time::Instant::now();
    let seed = now.elapsed().as_nanos();

    rand_pcg::Pcg64::new(0xcafef00dd15ea5e5 ^ seed, 0xa02bdbf7bb3c0a7ac28fa16a64abf96)
}
