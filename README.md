# r1cs-float

R1CS constraints for floating-point arithmetic.

## Disclaimer

This project is still in its early stages and hasn't been audited/reviewed by third parties. It may have some security flaws and side-channel vulnerabilities. Please DO NOT use this project in production unless you know what you are doing.

## Features

* Compatible with IEEE 754
    * Formats
        * [x] Single precision (`binary32`)
        * [x] Double precision (`binary64`)
        * [ ] Quadruple precision (`binary128`)
    * Values
        * [x] Signed zero (+0 and -0)
        * [x] Subnormal numbers
        * [x] Normal numbers
        * [x] Infinity
        * [x] NaNs
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
            * Rounding functions
                * [x] `trunc`
                * [x] `floor`
                * [x] `ceil`
                * [ ] `round`
* Highly optimized (C: Number of R1CS constraints, B: Number of bits queried to the lookup table)
    | Operation      | binary32  | binary64  |
    |----------------|-----------|-----------|
    | new            | 15C, 53B  | 15C, 114B |
    | neg, abs       | 0C, 0B    | 0C, 0B    |
    | add, sub       | 45C, 125B | 45C, 250B |
    | mul            | 36C, 145B | 36C, 299B |
    | div            | 45C, 149B | 45C, 303B |
    | sqrt           | 28C, 110B | 28C, 229B |
    | lt, gt, le, ge | 27C, 33B  | 27C, 65B  |
    | trunc          | 13C, 64B  | 13C, 128B |
    | ceil, round    | 20C, 64B  | 20C, 128B |

## Usage

TODO

## Tests

Simply run `cargo test`. Test datasets are generated using [TestFloat](https://github.com/ucb-bar/berkeley-testfloat-3).

## License

MIT
