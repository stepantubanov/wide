## README

Arithmetic operations on wider than native integer types (256 bit and more).

Current Status: Work In Progress.

Implements addition, subtraction, multiplication, division, formatting and parsing (dec and hex) in an efficient manner (targeting modern CPUs) and a number of basic bit operations (leading_zeros, etc).

Not ready for public use, not published. Tests are good, but docs are missing. Public API not completely thought through yet.

Only targeting x86-64 AVX2 capable CPUs at the moment. Therefore `target-cpu=native` or similar flag is required for compiling, either through .cargo/config or command line: `RUSTFLAGS="-C target-cpu=native" cargo build --release`.
