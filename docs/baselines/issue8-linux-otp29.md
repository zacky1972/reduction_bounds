# Issue 8: initial verification baseline

This is an observed baseline for stage 1, not a speedup claim. All representative
workloads and the ordinary full-suite command exited successfully.

## Reproduction

Measured source: `26ef0f27364dd9aef903b5c2d091626320eb50f1` (clean working tree).
Locked Lynx: `d74890ac7a446d57b762d0e4fcd3c848146b2ff6`.
Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0, Linux x86-64.

```sh
ERL_FLAGS='+S 4:4' LEAN_NUM_THREADS=4 \
  mix reduction_bounds.bench --repetitions 1 --max-cases 4 \
  --output docs/baselines/issue8-linux-otp29.json
```

The task used an isolated Mix build and removed its workspace afterward. Its
preparation took 36.213 seconds. The dependency's Lean build already
existed, so this is not a clean Lean/toolchain build measurement.

## Representative workloads

These are single command wall-time samples, including child VM startup. Peak
memory is the larger 100 ms sample of summed process-tree RSS across each pair;
shared pages can be counted multiple times. Each run used a fresh VM.

| Workload | Cold seconds | Warm attempt seconds | Sampled peak GiB |
| --- | ---: | ---: | ---: |
| `integer_cost` | 6.824 | 6.183 | 1.19 |
| `bound_transfer` | 12.339 | 12.473 | 1.48 |
| `list` | 2.339 | 2.239 | 1.12 |
| `circular_buffer` | 2.511 | 2.535 | 1.15 |
| `port` | 9.829 | 9.660 | 1.24 |
| `runner_empty` | 0.699 | 0.668 | 0.24 |
| `runner_runtime` | 1.548 | 1.455 | 0.98 |

All verification-cache hit counts were zero, as expected with the unchanged
`cache: false` policy. Warm attempts are not evidence of cache reuse. The
bound-transfer workload includes source inference followed by transfer, and
therefore has two verification requests.

## Full suite

- Command wall time: 1257.696 seconds.
- ExUnit: **280 passed** (18 documentation tests, 262 other tests); 1256.8 seconds total,
  12.4 seconds async, 1244.4 seconds sync.
- Sampled process-tree peak RSS: 3.57 GiB.
- Observed requests: 252 started, 248 completed, 2 raised, and 2 had no
  terminal event. Expected negative cases and task timeouts account for these
  latter events; they are not failed tests.
- Module reports: 275; persistent verification-cache hits: zero.

## Findings and next step

Most suite time was spent in synchronous tests. Integer and Port workflows also
spend several seconds in their postludes on every request. These observations
support prioritizing shared-theory artifacts and caching, then isolating fixtures
and parallelizing independent cases, as proposed in issue 8.

Summed completed runner-call time was 1263.842 seconds; its non-module remainder
was 190.393 seconds. The remainder includes process/Lake startup, shared-runtime
loading, protocol, and teardown, not just proof work. Request sums can overlap
in async tests and must not replace command wall time when comparing throughput.
Empty theorem-timing arrays are unavailable measurements, not zero-cost proofs.

The [JSON report](issue8-linux-otp29.json),
[full-suite events](issue8-linux-otp29_artifacts/suite_cold.jsonl), and
[full-suite log](issue8-linux-otp29_artifacts/suite_cold.log) retain the measurements.
Paths in the report describe the original run; use the corresponding files in
that directory after moving this checkout. See [benchmarking](../benchmarking.md)
for methodology and limitations. This single run does not establish a numerical
performance target or a statistically significant difference between cold and
warm attempts.
