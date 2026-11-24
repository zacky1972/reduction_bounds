# Issue 8: fixture isolation and selected concurrent tests

Measured source: `67eb4e5855be32bb2ab4d5b12b262263b69f50e3`, with a clean tree for all four measurements.
Linux x86-64, Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0, locked dependencies
unchanged. All runs used `ERL_FLAGS='+S 4:4'`, `LEAN_NUM_THREADS=2`, named modules,
artifact caching enabled and a per-VM Lean job budget of 2. Raw metadata retains
machine resources, versions, source status and selected test files.

## Implementation and coverage

Nine previously synchronous modules now run asynchronously: integer analysis,
integer cost bounds/cases, contract comparison/workflows, bound transfer, Port
completion/workflows/source proofs. The three integer fixtures are compiled once
by the helper and shared read-only, alongside the existing struct/Port fixtures.
Canonical fixture code is not recompiled or purged by individual test modules.
The changed-source regression still owns and mutates a private module.

The six contract workflow programs and five transfer programs are native ExUnit
parameter instances. Scenario inputs have one source of truth in support modules.
Assertions and scenario coverage are retained; the extracted contract/transfer
files have the same 42 and 48 assertion sites as before. Their execution counts
also match: each contract scenario performs three verification requests, and each
transfer scenario performs two. Event streams confirm inference, comparison and
transfer in dependency order in every parameter instance.

The original 312 reported tests become **322**: nine additional instances replace
two monolithic loops, and one regression checks parameter-aware profiling. There
are still 18 documentation tests. The production verification semantics, job
budget, cache controls, public target deadlines and negative-proof checks are
unchanged. Selected proof tests have a five-minute ExUnit allowance for multiple
queued invocations; the deliberate timeout tests retain their original deadlines.

## Same-source selected-suite comparison

The selected files contain 36 tests across Port completion, contract workflows
and bound transfer. Repeat these separately, changing only `--max-cases` and the
output path:

```sh
ERL_FLAGS='+S 4:4' LEAN_NUM_THREADS=2 \
  REDUCTION_BOUNDS_LEAN_JOBS=2 REDUCTION_BOUNDS_PROOF_MODE=named \
  REDUCTION_BOUNDS_PROOF_CACHE=on \
  mix reduction_bounds.bench --suite-only --seed 0 --max-cases 4 \
  --test-files test/reduction_bounds/port_completion_proof_test.exs,test/reduction_bounds/contract_workflow_test.exs,test/reduction_bounds/bound_transfer_test.exs \
  --output _build/selected-parallel.json
```

`max_cases=1` provides a serial reference for the same code, immutable fixtures,
programs and assertions. The cases are registered as asynchronous in both runs;
the concurrency limit serializes their execution in the reference. Each run
prepares an isolated build and runner and starts with an empty verification
cache. Existing dependency Lean build artifacts are reused. No tests or checks
ran concurrently with these measurements.

| ExUnit max cases | Command wall, s | Sampled peak RSS, GiB | Peak admitted jobs | Observed runner calls | Passed tests |
| --- | ---: | ---: | ---: | ---: | ---: |
| 1 | 259.340 | 1.37 | 1 | 67 | 36 |
| 4 | 154.334 | 2.48 | 2 | 67 | 36 |

The parallel selected run was **40.5% shorter** in this pair of measurements.
This is one cold-cache sample per configuration, not a statistical performance
guarantee or an estimate of a whole-suite speedup. Cache flags and request counts
are retained in the raw reports. Memory is a sampled process-tree sum and can
count shared pages repeatedly.

## Full-suite validation

Both ordinary full-suite runs passed **322 tests** (18 documentation tests and
304 other tests). Neither trace mode nor slowest-test mode was enabled.

| Seed | ExUnit max cases | Command wall, s | ExUnit async phase, s | ExUnit sync phase, s | Sampled RSS, GiB | Peak admitted jobs |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| 0 | 4 | 728.528 | 349.860 | 377.757 | 2.46 | 2 |
| 42 | 24 | 723.590 | 351.164 | 371.590 | 2.63 | 2 |

Reproduce with the same environment as above, removing `--test-files` and using
the corresponding seed and maximum-case settings. Each run has its own isolated
build and cold verification cache. The default Lean job budget remains 2 even
when ExUnit schedules up to 24 cases.

All eleven parameter identities are distinct in the profiler and all preserve
their required request order in both full runs. Source/callee replay, changed
BEAM rejection, altered-bound and axiom/unfinished-proof rejection, queueing,
timeout, cancellation and restart tests remain enabled. Expected failed and
unfinished request events from negative/timeout tests are not test failures.

These full runs use different seeds and scheduling limits and are correctness
checks across those settings, not a controlled comparison between max cases 4
and 24. The earlier stage-4a profile used a different test organization and target
module identities; do not attribute its entire timing difference to concurrency.
The selected same-source comparison above isolates scheduling more closely.

## Remaining work

Cache-policy, measurement/environment mutation, worker/preparation coordination,
restart and independent-VM publication tests remain synchronous. Other proof-only
families can be audited incrementally. Keep a useful number of independent
scenarios ready for the bounded verifier rather than increasing runnable work
without regard to queueing or memory. Higher case counts can increase individual
test latency while improving aggregate throughput.

A persistent runner pool or request batching still requires separate evidence
and a supported Lynx interface. This stage does not reuse mutable Lean sessions
or alter proof-assumption checks. See [fixture ownership and scheduling](../test_concurrency.md)
and [profiling and the job budget](../job_budget.md).

## Validation evidence

- Both full suites: 322 passed, seeds 0 and 42, case limits 4 and 24.
- Both selected suites: 36 passed, case limits 1 and 4.
- Reporting regressions: 6 passed, including distinct parameter identities and
  invalid selected-suite arguments.
- `mix check` and `mix docs --warnings-as-errors` passed.

Raw reports:

- [Serial selected suite](issue8-fixtures-selected-1.json)
- [Parallel selected suite](issue8-fixtures-selected-4.json)
- [Full suite, seed 0 / max cases 4](issue8-fixtures-full-4.json)
- [Full suite, seed 42 / max cases 24](issue8-fixtures-full-24.json)

Each report has a matching `_artifacts` directory containing preparation logs,
command output and event streams. Absolute paths describe the original run;
use the adjacent artifacts after moving the checkout.

[Reporting tests](issue8-fixtures-validation_artifacts/reporting.log),
[static checks](issue8-fixtures-validation_artifacts/check.log),
[documentation build](issue8-fixtures-validation_artifacts/docs.log).
