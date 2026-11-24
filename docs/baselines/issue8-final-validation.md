# Issue 8: final policy validation

Final policy: named modules and eligible shared/target artifact caching remain
enabled. The reference M2 Max profile is 4 jobs with 2 Lean threads; the portable
fallback remains 2 jobs and Lean threads remain caller-controlled. Public target
deadlines, proof assertions, embedded comparisons and cache-bypass paths remain
unchanged. The [Mac calibration](issue8-mac-job-calibration.md) supplies the
controlled performance evidence.

## Finalization review

Reviewed remote branch `8` at `6ff038cebf09969e38498957e83393193527ba6a` and the
maintainer's [published policy](https://github.com/zacky1972/reduction_bounds/issues/8#issuecomment-7128848077).
Production source files and test files match that remote snapshot. Finalization
changes documentation, documentation extras and the recorded evidence; it does
not introduce another optimization or change runtime settings automatically.
The issue remains open for isolated startup/import attribution.

## Local full-suite regression run

Tested clean local snapshot `e578bcab90f34f8b31e982d6b69f802dc6fae14a` on Linux
x86-64, OTP 29.1.2, Elixir 1.20.5, Lean 4.35.0 and the unchanged locked Lynx
dependency. This local snapshot includes the already published isolated-build
resource and preparation-test timeout fixes as well as the policy documentation.

```sh
ERL_FLAGS='+S 4:4' REDUCTION_BOUNDS_LEAN_JOBS=4 LEAN_NUM_THREADS=2 \
  REDUCTION_BOUNDS_PROOF_MODE=named REDUCTION_BOUNDS_PROOF_CACHE=on \
  mix test --seed 42 --max-cases 24
```

All **345 tests passed** (18 documentation tests and 327 other tests), exit status
0, with no warnings. ExUnit reports 313.5 seconds: 236.8 asynchronous and 76.6
synchronous (rounded phase times need not sum to the rounded total). External
command elapsed time is 314.466 seconds.

The normal pre-existing test cache was used, and benchmark event recording was
disabled. This is correctness validation at another seed, not a controlled cold
or warm benchmark and not a comparison with the Mac timings. See the
[suite log](issue8-final-suite.log) and [execution metadata](issue8-final-suite.json).

## Required checks

- `mix check` passed: dependency audit, compilation with warnings as errors,
  formatting, strict Credo, unused-lock checks, spelling and Dialyzer.
- `mix docs --warnings-as-errors` passed.
- `git diff --check` passed.

The [static-check log](issue8-final-check.log) records the required alias run.
Only validation records and documentation links were added after the tested
snapshot. No source or test behavior changed after this full-suite run.
