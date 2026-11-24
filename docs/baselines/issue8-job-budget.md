# Issue 8: synchronous profiling and a global job budget

The implementation adds a per-VM verification budget (default 2), ordinary ExUnit
profiling, request/test attribution, source-generation spans, and sampled process-tree
CPU clocks alongside RSS. It retains one-shot Lynx verification and existing test
concurrency settings. No fixture parallelization or persistent runner pool is added.

## Sources and environment

- Suite profile: `d4117f9daf42954f54f465af6ee221e163056a9c`.
- Job comparison: `060b7d76109e6ae17ed2fafc6d46bdcc47c5274c`.
- Both measurements started with clean source trees. The later revision adds an
  empty-workload selection guard and clarifies event-recording limitations; its
  verification runtime is unchanged from the suite profile.
- Linux x86-64, Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0; locked dependencies unchanged.
- 9 reported processors, approximately 9.73 GiB RAM,
  `ERL_FLAGS='+S 4:4'`. The suite used 2 Lean threads and job limit 2; the job
  comparison held Lean threads at 1 and varied only the job limit.

The existing dependency Lean build was reused. Each benchmark prepared an isolated
Mix build and explicitly built the runner before verification measurements.
No test/check command ran concurrently with these measurements. Raw reports retain
versions, source status, environment settings and preparation costs.

## Ordinary full-suite profile

```sh
ERL_FLAGS='+S 4:4' LEAN_NUM_THREADS=2 REDUCTION_BOUNDS_LEAN_JOBS=2 \
  mix reduction_bounds.bench --suite-only --seed 0 --max-cases 4 \
  --output _build/issue8-job-suite.json
```

The verification cache started empty. This is an ordinary run without trace mode.
**312 tests passed**: 18 documentation tests and 294 other tests.

| Measurement | Observed value |
| --- | ---: |
| Command wall time | 981.073 s |
| ExUnit run | 980.133 s |
| ExUnit asynchronous phase | 16.663 s |
| ExUnit synchronous phase | 963.470 s |
| Sampled peak process-tree RSS | 2.43 GiB |
| Sampled CPU / command wall time | 93.5% of one core |
| Observed runner calls started | 299 |
| Peak admitted slots observed at runner calls | 2 |
| Observed cached module reports | 1057 |

Approximately 98.3% of ExUnit run time remains in the synchronous phase. The
admitted requests' aggregate job-queue wait was only 4.253 ms.
Increasing the budget alone does not expose independent work inside synchronous
modules and sequential scenario loops.

Completed-request and instrumented-source duration sums:

| Measurement | Sum |
| --- | ---: |
| Public source generation | 0.407 s |
| Shared proof input and translation registration | 0.096 s |
| Verification assembly/finalization | 0.373 s |
| Preparation identity lookup and waiting | 27.446 s |
| Supervised runner-call wall time | 974.926 s |
| Reported module time | 759.635 s |
| Runner-call remainder after reported module time | 215.291 s |

These are overlapping request sums, not a partition of suite elapsed time.
Source spans cover the instrumented public producers, not every test helper or
fixture operation. The runner remainder combines startup, imports, artifact
loading, protocol, dispatch and teardown; this measurement does not isolate
process startup. Cached reports may assign no module elaboration time while
artifact loading still takes wall time.

The event stream has two intentionally failed translation requests, plus four
starts without terminal events: two running-target timeouts and two queued-target
timeouts. Their tests passed. Recorder tests that redirect or disable measurement
are absent from request aggregates but remain in native test timings.

### Modules with the largest summed test durations

All ten are currently synchronous. Native test durations exclude module setup,
cleanup and loading. Module sums are not full-suite throughput measurements.

| Module | Tests | Summed test duration, s |
| --- | ---: | ---: |
| `ReductionBounds.ProofFamiliesTest` | 8 | 107.321 |
| `ReductionBounds.IntegerCostBoundTest` | 24 | 99.077 |
| `ReductionBounds.BoundTransferTest` | 11 | 95.656 |
| `ReductionBounds.PortCompletionProofTest` | 11 | 93.051 |
| `ReductionBounds.PortWorkflowTest` | 14 | 86.153 |
| `ReductionBounds.ContractWorkflowTest` | 5 | 63.866 |
| `ReductionBounds.ProofCacheTest` | 5 | 61.262 |
| `ReductionBoundsTest` | 23 | 55.464 |
| `ReductionBounds.PortSourceProofTest` | 9 | 52.164 |
| `ReductionBounds.ContractComparisonTest` | 12 | 49.960 |

### Expensive individual tests

The request count is the number of observed completed verification requests
attributed to the test. Concurrent request durations can overlap.

| Test | Duration, s | Requests |
| --- | ---: | ---: |
| `ReductionBounds.ContractWorkflowTest`: public workflows report checked bounds and their assumptions for representative programs | 54.543 | 18 |
| `ReductionBounds.BoundTransferTest`: rechecks and transfers arithmetic, branches, CRC expressions, and finite recursion | 30.358 | 10 |
| `ReductionBounds.ProofFamiliesTest`: integer theories verify through named, reused, bypassed, and embedded paths | 22.362 | 4 |
| `ReductionBounds.IntegerCostBoundTest`: checks compiled arithmetic around signed power-of-two boundaries | 21.643 | 8 |
| `ReductionBounds.ProofFamiliesTest`: protocol theories verify through named, reused, bypassed, and embedded paths | 21.133 | 4 |
| `ReductionBounds.ContractComparisonTest`: ordering certificates cover multiplication and structural padding | 20.368 | 7 |
| `ReductionBounds.ProtocolCostProofTest`: Lean rejects changed formulas, counters, unsupported size evidence and unfinished proofs | 18.076 | 4 |
| `ReductionBounds.PortCompletionProofTest`: Lean rejects altered transitions, budget evidence and unfinished completion proofs | 17.893 | 3 |

## Controlled job-budget probe

```sh
ERL_FLAGS='+S 4:4' LEAN_NUM_THREADS=1 \
  REDUCTION_BOUNDS_PROOF_MODE=named REDUCTION_BOUNDS_PROOF_CACHE=on \
  REDUCTION_BOUNDS_LEAN_JOBS=2 \
  mix reduction_bounds.bench --no-suite --workloads concurrent_integer \
  --repetitions 3 --max-cases 4 --seed 0 --output _build/issue8-jobs-2.json
```

Repeat separately with limits 1 and 4. Each run prepares a shared integer theory,
then submits four independent target proofs concurrently. Each variant has one
cold-cache attempt and three warm attempts in fresh VMs. Every attempt includes
five runner calls: one preparation proof followed by the four target proofs.
All 12 commands and all 60 verification requests succeeded, with no unfinished
requests and no observed admission exceeding the configured limit.

| Job limit | Cold command, s | Warm median, s | Maximum sampled RSS, GiB | Peak admission |
| --- | ---: | ---: | ---: | ---: |
| 1 | 15.757 | 8.180 | 1.27 | 1 |
| 2 | 11.364 | 5.347 | 2.24 | 2 |
| 4 | 9.967 | 4.117 | 4.11 | 4 |

Warm medians use three samples; RSS maxima include cold and warm attempts. This
probe demonstrates bounded concurrency and its memory trade-off, not a full-suite
speedup. The default remains 2 pending fixture isolation and representative
multi-family concurrency measurements. More RAM on another machine does not
establish its optimal CPU concurrency.

CPU clocks are sampled and may lose short-lived work or sub-second CPU time,
especially with Linux's clock precision. The CPU percentage is an estimate
relative to one core, not an exact machine utilization measurement. RSS sums
can count shared pages repeatedly. See [profiling and the budget](../job_budget.md).

## Priorities for the next stage

1. Audit proof-only modules such as `PortCompletionProofTest` and
   `ContractComparisonTest` for a first bounded asynchronous pilot. Preserve all
   negative proofs and source/axiom audits.
2. Isolate compiled fixtures before parallelizing integer-cost, transfer and
   Port workflows. Compile immutable fixtures once or give independently running
   groups distinct module names; one group's cleanup must not purge another's code.
3. Split the independent program scenarios in the contract workflow (18 observed
   requests in one test) and transfer loop (10). Keep inference, comparison and
   transfer in dependency order within each scenario.
4. Keep cache controls, event-destination changes, and supervisor-restart tests
   under deliberate serialization. A global runner cap does not isolate fixtures.
5. Investigate the runner remainder separately before choosing a supported Lynx
   batching/session API. Do not treat the entire remainder as startup cost.

The suite measurement is not a before/after speedup comparison with earlier Linux
or Mac runs: test counts, thread settings, cache lifecycle and machines differ.
This stage establishes observation and resource control for the concurrency work.

## Validation and raw evidence

- Ordinary full suite: 312 passed, seed 0, maximum 4 ExUnit cases.
- Focused budget, preparation, boundary and reporting tests: 20 passed, seed 42,
  including the subsequent empty-workload validation regression.
- `mix check` and `mix docs --warnings-as-errors` passed.
- Tests cover owner/worker termination, cancelled queued callers, queue-inclusive
  target deadlines, error propagation, shared-preparation/job-budget interaction,
  and terminating old workers before budget restart.

[Full suite report](issue8-job-suite.json),
[full suite output](issue8-job-suite_artifacts/suite_cold.log),
[focused tests](issue8-job-validation_artifacts/focused.log),
[static checks](issue8-job-validation_artifacts/check.log),
[documentation build](issue8-job-validation_artifacts/docs.log).

Job probes: [limit 1](issue8-jobs-1.json), [limit 2](issue8-jobs-2.json),
[limit 4](issue8-jobs-4.json). Matching `_artifacts` directories retain command
output and event streams. Absolute paths in JSON identify the original run;
use the adjacent artifacts after moving the checkout.
