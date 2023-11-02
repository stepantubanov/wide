## README

NOTE: Contains unsound unsafe code due to out of bounds reads.

Arithmetic operations on wider than native integer types (256 bit and more).

Current Status: Work In Progress.

Implements addition, subtraction, multiplication, division, formatting and parsing (dec and hex) in an efficient manner (targeting modern CPUs) and a number of basic bit operations (leading_zeros, etc).

Not ready for public use, not published. Tests are good, but docs are missing. Public API not completely thought through yet.

Only targeting x86-64 AVX2 capable CPUs at the moment. Therefore `target-cpu=native` or similar flag is required for compiling, either through .cargo/config or command line: `RUSTFLAGS="-C target-cpu=native" cargo build --release`.

u64, u128 format/parse functions faster than Rust stdlib as number gets larger. Example (last number in bench name is upper bound of decimal digits, which means it tests random numbers from 0 to 10\*\*n):

```
parse_u64/uint/3        time:   [3.3472 us 3.3913 us 3.4379 us]
parse_u64/std/3         time:   [4.4845 us 4.5245 us 4.5717 us]

parse_u64/uint/8        time:   [3.3039 us 3.3462 us 3.3929 us]
parse_u64/std/8         time:   [9.4734 us 9.5557 us 9.6475 us]

parse_u64/uint/18       time:   [6.1510 us 6.2355 us 6.3346 us]
parse_u64/std/18        time:   [19.219 us 19.435 us 19.658 us]
```
