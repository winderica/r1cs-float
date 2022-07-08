# r1cs-float

R1CS constraints for floating-point arithmetic.

## Disclaimer

This project is still in its early stages and hasn't been audited/reviewed by third parties. It may have some security flaws and side-channel vulnerabilities. Please DO NOT use this project in production unless you know what you are doing.

## Features

* Compatible with IEEE 754
    * Formats
        * [ ] Single precision (`binary32`)
        * [x] Double precision (`binary64`)
        * [ ] Quadruple precision (`binary128`)
    * Values
        * [x] Signed zero (+0 and -0)
        * [x] Subnormal numbers
        * [x] Normal numbers
        * [ ] Infinity
        * [ ] NaNs
    * Operations
        * Mathematical operations
            * [x] `add`
            * [x] `sub`
            * [x] `mul`
            * [x] `div`
            * [x] `neg`
            * [x] `abs`
            * [ ] `rem`
            * [ ] `fma`
            * Exponential functions
                * [x] `sqrt`
                * [ ] `pow`
                * [ ] etc.
            * [ ] Logarithm functions (`ln`, `log2`, etc.)
            * [ ] Trigonometric functions (`sin`, `cos`, etc.)
        * Comparisons
            * [x] `eq`
            * [x] `lt`, `gt`, `le`, `ge`
            * [ ] `min`, `max`
        * Conversions
            * [ ] Rounding functions (`ceil`, `floor`, etc.)
* Highly optimized
    * `f64::{add, sub}`: 378 constraints
    * `f64::mul`: 347 constraints
    * `f64::div`: 563 constraints
    * `f64::sqrt`: 439 constraints
    * `f64::{lt, gt, le, ge}`: 86 constraints

## Usage

TODO

## Tests

Simply run `cargo test`. Test datasets are generated using [TestFloat](https://github.com/ucb-bar/berkeley-testfloat-3).

## License

MIT