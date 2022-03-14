use criterion::measurement::WallTime;
use criterion::{criterion_group, criterion_main, BenchmarkGroup, BenchmarkId, Criterion};
use rand::distributions::uniform::SampleUniform;
//use rand::prelude::*;
use rand::{distributions::Uniform, Rng};
use std::convert::identity;
use std::fmt::Write;
use std::ops::Range;
use std::time::{Duration, Instant};

use wide::{u256, u64_ext::*};

pub type U128 = wide::Wide<2>;

fn rng() -> rand_pcg::Pcg64 {
    let t = Instant::now().elapsed().as_nanos();
    rand_pcg::Pcg64::new(0xcafef00dd15ea5e5 ^ t, 0xa02bdbf7bb3c0a7ac28fa16a64abf96)
}

struct Bench<'a, 'b, T> {
    group: &'a mut BenchmarkGroup<'b, WallTime>,
    items: Vec<T>,
}

impl<'a, 'b, T> Bench<'a, 'b, T> {
    fn with<R, F>(
        group: &'a mut BenchmarkGroup<'b, WallTime>,
        len: usize,
        range: Range<R>,
        f: F,
    ) -> Self
    where
        R: SampleUniform,
        F: FnMut(R) -> T,
    {
        let distr = Uniform::from(range);
        let mut rng = rng();

        let items = (0..len)
            .map(|_| rng.sample(&distr))
            .map(f)
            .collect::<Vec<_>>();

        Bench { group, items }
    }

    fn register(&mut self, name: &str, param: usize, mut f: impl FnMut(&T) -> u64) {
        self.group
            .bench_with_input(BenchmarkId::new(name, param), &self.items, |b, items| {
                b.iter(|| {
                    let mut sum = 0;
                    for item in items.iter() {
                        sum += f(item);
                    }
                    sum
                })
            });
    }
}

pub fn bench_parse(c: &mut Criterion) {
    let mut group = c.benchmark_group("parse_u64");

    group
        .warm_up_time(Duration::from_millis(350))
        .measurement_time(Duration::from_secs(2));

    for i in [3, 8, 18] {
        let input_range = 0..10_u64.pow(i as u32);

        let mut bench = Bench::with(&mut group, 1000, input_range, |n| n.to_string());

        bench.register("uint", i, |s| u64::from_str_dec(s).unwrap());

        bench.register("std", i, |s| str::parse::<u64>(s).unwrap());
    }

    group.finish();
}

pub fn bench_format(c: &mut Criterion) {
    let mut group = c.benchmark_group("format_u64");

    group
        .warm_up_time(Duration::from_millis(350))
        .measurement_time(Duration::from_secs(2));

    let mut out = String::with_capacity(1024);

    for i in [3, 8, 18] {
        let input_range = 0..10_u64.pow(i as u32);

        let mut bench = Bench::with(&mut group, 1000, input_range, identity);

        bench.register("uint", i, |&n| {
            out.clear();
            write!(&mut out, "{}", SimdFormatted(n)).unwrap();
            out.len() as u64
        });

        bench.register("std", i, |&n| {
            out.clear();
            write!(&mut out, "{}", n).unwrap();
            out.len() as u64
        });
    }

    group.finish();
}

pub fn bench_format_u128(c: &mut Criterion) {
    let mut group = c.benchmark_group("format_u128");

    group
        .warm_up_time(Duration::from_millis(350))
        .measurement_time(Duration::from_secs(2));

    let mut out = String::with_capacity(1024);

    for i in [10, 25, 30] {
        let input_range = 0..10_u128.pow(i as u32);

        let mut bench = Bench::with(&mut group, 1000, input_range, identity);

        bench.register("uint", i, |&n| {
            out.clear();
            write!(&mut out, "{}", U128::from_u128(n)).unwrap();
            out.len() as u64
        });

        bench.register("std", i, |&n| {
            out.clear();
            write!(&mut out, "{}", n).unwrap();
            out.len() as u64
        });
    }

    group.finish();
}

pub fn bench_div_u256(c: &mut Criterion) {
    let mut group = c.benchmark_group("div_u256");

    group
        .warm_up_time(Duration::from_millis(350))
        .measurement_time(Duration::from_secs(2));

    for i in [3] {
        let input_range = 0..10_u128.pow(30);

        let mut bench = Bench::with(&mut group, 100, input_range, |n| {
            u256::from_u128(n).pow(i as u32)
        });

        let mut divisor = 0xff_u64;

        bench.register("uint", i, |n| {
            let q = n / divisor;
            divisor = divisor.wrapping_add(0xff);

            q.0[0]
        });
    }

    group.finish();
}

criterion_group!(
    benches,
    bench_parse,
    bench_format,
    bench_format_u128,
    bench_div_u256
);
criterion_main!(benches);
