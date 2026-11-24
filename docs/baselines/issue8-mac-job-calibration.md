<!-- cspell:words doctests -->
# Issue 8: reference Mac job-budget calibration

Measured on 2026-11-24 by the maintainer on a 14-inch 2023 MacBook Pro,
Apple M2 Max, 96 GB RAM, 12 cores (8 performance, 4 efficiency). The supplied
[original JSON report](issue8-mac-job-calibration.json) records clean source
`6ff038cebf09969e38498957e83393193527ba6a`, OTP 29.1.2, Elixir 1.20.5,
Lean 4.35.0 and locked Lynx `d74890ac7a446d57b762d0e4fcd3c848146b2ff6`.

## Controlled settings

Both configurations use named modules, shared/target caching enabled,
`LEAN_NUM_THREADS=2`, seed 0, ExUnit max_cases 24 and the unchanged public
60,000 ms target deadline. BEAM scheduler override variables are unset; the
report records 12 schedulers online. Jobs 2 runs first, then jobs 4. Each has
an isolated Mix build, runner preparation, one cold verification-cache run and
one warm run in a fresh VM. Dependency build artifacts can already be warm.

The comparison is valid (`comparable: true`, no issues). All four suite commands
exit successfully and record 345 tests (18 doctests and 327 tests), with 299
runner calls each. This is one paired trial, not a distribution or a comparison
of every possible job/thread combination.

## Results

| Jobs | Verification cache | Command seconds | Maximum sampled RSS, GiB | Observed jobs |
| ---: | --- | ---: | ---: | ---: |
| 2 | cold | 535.565 | 1.99 | 2 |
| 2 | warm | 420.160 | 1.99 | 2 |
| 4 | cold | 339.609 | 3.76 | 4 |
| 4 | warm | 277.794 | 3.55 | 4 |

Relative to jobs 2, jobs 4 reduces cold command time by **36.6%** (195.956
seconds) and warm time by **33.9%** (142.366 seconds). These percentages compare
the same phase in this trial, not historical ordinary runs with different tests.
Memory is a 100 ms sampled sum across the process tree and may count shared
pages repeatedly; it is not a measurement of unique physical memory.

Aggregate admission waiting falls from 5,611.909 to 2,453.998 seconds cold and
4,487.533 to 2,128.025 seconds warm. These sums overlap across requests and are
not components of elapsed time. Aggregate actual runner-call time is 922.199
versus 937.394 seconds cold and 715.352 versus 759.471 seconds warm. Thus the
shorter suite time does not imply less aggregate runner work or faster individual
proof elaboration; increased concurrency permits more overlap.

Each passing suite records two failed request events and four unfinished request
events. Negative-proof and cancellation tests deliberately exercise those paths;
the suite exit status determines test success. Warm runs each report 1,248 cached
modules; cold counts are 1,050 and 1,048, so scheduling is not assumed to produce
identical cache-hit counts.

## Decision and limits

Use `REDUCTION_BOUNDS_LEAN_JOBS=4 LEAN_NUM_THREADS=2` as the initial profile for
this reference Mac. Keep the portable fallback at 2 for compatibility on
unmeasured machines, without calling it optimal. Repeat with rotated order before
making a stronger default claim. Other thread counts and job limits remain
untested in this controlled full-suite comparison. No further long calibration
is required merely to record this result.

Earlier attempts remain unsuccessful evidence: temporary-path relative links
first prevented packaged Lean sources from loading; copying `priv` before timed
runs fixes that. The next attempt had one jobs-2 cold failure in a nested
`Task.async_stream` 60-second limit. The test now relies on its existing ExUnit
300-second bound. Its coalescing assertions and the public API deadlines remain
unchanged. Do not combine those failed timings with this valid trial.

The original JSON is retained unchanged, including machine-local artifact paths.
Those paths are historical metadata, not bundled suite logs or JSONL files.
Only the supplied report and the maintainer's failure log were available for
this review; do not describe it as an independent replay of all raw events.
