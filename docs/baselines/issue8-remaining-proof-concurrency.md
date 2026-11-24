# Issue 8: remaining independent proof-test concurrency

Measured source: `5f994a4`, clean for all four runs. The implementation was
reviewed against remote branch `8` at `44afdc9d6ec5826c5e84ffe80b87193cd2a8a6ba`
and the revised Issue 8 plan. Linux x86-64, Elixir 1.20.5, OTP 29.1.2,
Lean 4.35.0, locked dependencies unchanged. All runs used
`ERL_FLAGS='+S 4:4'`, `LEAN_NUM_THREADS=2`, named modules and artifact caching.
Each command prepared its own isolated build/verification cache and runner;
existing dependency Lean build artifacts were reused. No other tests or checks
ran concurrently with measurement. Full toolchain and machine metadata is in
all four JSON reports.

## Scope and isolation

Six previously synchronous modules now use asynchronous ExUnit scheduling:
protocol proofs, protocol-condition proofs, protocol-cost proofs, integer-size
proofs, execution comparison and struct bounds. Request-local contracts,
observations and strings are immutable. Packaged Lean sources are read only.
Struct tests use the canonical bounded-counter module and immutable BEAM compiled
once in the test helper; they never recompile or purge that module. None of the
six modules changes environment variables, cache settings or supervisors.

Three positive Protocol-family loops become eleven native parameter instances
(5 protocol, 3 condition, 3 cost), sharing each file's pure support functions and
single scenario list. Their profiler identities contain the scenario parameter
and match ExUnit's identities. All original assertion sites are retained:
protocol 9, conditions 8, cost 11, integer size 7, struct 16, execution comparison 7.
The selected cohort grows from 32 reported tests to 40, while retaining exactly
47 runner calls. The full suite grows from 328 to 336 tests (18 documentation tests and
318 other tests), because eleven instances replace three loops.

Integer-size comprehensions that construct one combined Lean proof stay together.
Negative variants, theorem/axiom audits, changed-source rejection and scenario
sequencing remain intact. All verification still passes through the existing
per-VM job budget. No production proof source, cache semantics, Lean options,
public target deadlines or deliberate timeout tests changed. The default job
budget remains a provisional 2. New asynchronous multi-request cases use the
existing five-minute ExUnit scheduling allowance; execution comparison retains
its two-minute allowance.

## Same-source selected-suite comparison

These six files were selected in all cohort runs:

- `test/reduction_bounds/protocol_proof_test.exs`
- `test/reduction_bounds/protocol_conditions_proof_test.exs`
- `test/reduction_bounds/protocol_cost_proof_test.exs`
- `test/reduction_bounds/integer_size_proof_test.exs`
- `test/reduction_bounds/execution_comparison_test.exs`
- `test/reduction_bounds/struct_bound_test.exs`

Both controlled samples used seed 0, jobs 2, threads 2 and an empty verification
cache. Only ExUnit max cases and the output path differed. `max_cases=1` serializes
the same asynchronous cases, scenarios and assertions without a separate code path.

| ExUnit max cases | Command seconds | Sampled peak RSS, GiB | Sampled CPU, % | Peak admitted jobs | Runner calls | Passed |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 150.218 | 1.380 | 90.5 | 1 | 47 | 40 |
| 4 | 80.712 | 2.794 | 180.9 | 2 | 47 | 40 |

The parallel selected sample was **46.3% shorter**, with higher sampled memory.
This is one cold sample per configuration, not a statistical guarantee or a
whole-suite/Mac speedup estimate. Both runs reported 120 cached module reports;
artifact reuse within each suite is possible even though each suite starts cold.
CPU 100% represents one core. RSS is a sampled sum and can count shared pages
repeatedly; neither is exact OS accounting.

Reproduce with `mix reduction_bounds.bench --suite-only --seed 0 --max-cases 4`,
`--test-files` containing the six comma-separated paths above, and a new
`--output`. Set the environment shown above and
`REDUCTION_BOUNDS_LEAN_JOBS=2`. Repeat separately with `--max-cases 1` and another
output path. Do not use trace or slowest-test mode to measure parallel throughput.

## Additional correctness checks

| Scope | Seed | ExUnit max cases | Jobs | Command seconds | Sampled RSS, GiB | Passed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Selected six files | 42 | 24 | 4 | 54.011 | 4.521 | 40 |
| Ordinary full suite | 42 | 4 | 2 | 650.250 | 2.609 | 336 |

The selected seed-42 run reached four admitted jobs. Its seed, case count and job
budget differ from the controlled pair; do not attribute the difference to any
single setting or use it to select a default. These are correctness checks,
not a completed job-budget calibration.

The full suite's ExUnit interval was 649.514 seconds: 420.039 async and 229.475
sync. All 336 tests passed, including cache invalidation, negative/unfinished
proofs, source/callee replay, API errors, queueing, cancellation and restart tests.
The full run observed 299 runner calls and a peak admission of 2. This is one
full-suite seed/case configuration; a cold full suite with jobs 2/max_cases 24
was not validated in this stage. Earlier calibration had deadline failures at
that setting. No deadlines were increased to hide overload.

All eleven new parameter identities are distinct in all four event streams,
with exactly one completed successful verification per instance. The full run
also retains six original contract workflow identities with three requests each
and five bound-transfer identities with two requests each. Existing parameter
labels are unchanged. Expected negative-proof and deliberate-timeout request
events are distinct from test failures.

## Remaining work and validation

Cache-policy, environment/recorder mutation, worker/preparation coordination,
supervisor restart and independent-VM publication modules remain synchronous.
Their isolation is a separate milestone. Recheck job/thread settings on the
target Mac after this scheduling change. Persistent runner reuse and cold DAG
scheduling remain conditional on profiling; no optimum or universal speedup is
claimed here.

`mix check` and `mix docs --warnings-as-errors` passed before measurements. A
compile-only pass excluded all 40 selected tests and emitted no warnings; it is
not counted as a proof validation. The four measured suites above provide the
actual proof checks. Final documentation/format/spelling checks cover this report.

Raw reports (each has adjacent logs and JSONL events in its matching `_artifacts`
directory):

- [Serial cohort](issue8-remaining-serial.json)
- [Parallel cohort](issue8-remaining-parallel.json)
- [Second seed and higher concurrency](issue8-remaining-seed42.json)
- [Full suite](issue8-remaining-full.json)

Absolute paths in raw reports describe the original workspace; use the adjacent
artifacts after relocating the checkout. Test/source data and all accepted/rejected
claims are retained; moving tests changes scheduling and reported case counts.

[Static checks](issue8-remaining-validation_artifacts/check.log),
[initial documentation build](issue8-remaining-validation_artifacts/docs.log),
[compile-only check](issue8-remaining-validation_artifacts/compile-only.log).
