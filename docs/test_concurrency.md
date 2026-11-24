# Fixture isolation and selected concurrent tests

The selected proof tests now run asynchronously under the existing per-VM Lean
job budget. The provisional default budget remains 2; it has not been calibrated as an optimum. ExUnit `max_cases` controls test-case
scheduling, while the job budget controls aggregate verification invocations.
Neither setting changes Lean's own thread count.

The later [reference-Mac calibration](baselines/issue8-mac-job-calibration.md)
supports an initial profile of 4 jobs with 2 Lean threads on the measured M2 Max.
This does not change the portable fallback or establish a universal optimum.

## Immutable and mutable fixtures

`test_helper.exs` compiles the integer analysis, integer-cost and arithmetic-case
fixtures once and retains their BEAM binaries alongside the existing struct and
Port fixtures. Their consumers share the same module identities and read-only
binaries. Test modules no longer recompile or purge these shared fixtures.
Fixture source files remain the single source of their implementations.

Integer analysis/cost/case tests and contract/transfer workflows use this immutable
registry. Contract and transfer workflows previously compiled private copies;
they now use the same canonical fixtures. Public claims, input ranges, source
replay checks and assertions are retained with the corresponding target module
identity. Native function evaluation still checks inferred results against the
loaded fixture implementations.

The changed-source transfer test retains its mutable fixture under its own test
module's namespace. It recompiles and unloads only that private module, and still
rejects the old bound against the changed BEAM. Other tests cannot purge shared
fixture code when their module finishes.

## Selected asynchronous modules

- Integer analysis, integer cost bounds, and arithmetic/CRC cost cases.
- Contract comparison and contract workflows.
- Bound transfer.
- Port completion proofs, Port workflows, and Port source proofs.

Proof-only modules use request-local values and independent runner environments.
The selected Port consumers read immutable fixtures compiled by the helper.
Their optional report flag is read only; these tests do not change environment
variables, cache configuration or global supervisors.

Recorder/environment mutation tests, shared-preparation unit tests,
worker-budget/restart tests, and independent-VM publication tests retain their
existing synchronous execution. The job budget does not isolate fixture names or
mutable global state, and does not impose a machine-wide limit on separate VMs.

## Independently scheduled scenarios

The contract workflow's six programs and transfer loop's five programs are now
native ExUnit parameterized cases. `async: true` lets different parameter instances
run concurrently. Merely splitting a loop into ordinary tests inside one module
would not do this. The scenario lists and their inputs each have one source of
truth in the corresponding support module.

Each contract scenario still performs inference, contract comparison, then transfer
in that order. Each transfer scenario still infers its source bound before checking
the transfer. All result, assumption, theorem-name and error assertions remain.
The eleven independently scheduled instances replace two monolithic tests; this
adds nine reported tests without adding or dropping program scenarios.

The selected cases and existing asynchronous normalization, execution and periodic
proof cases allow up to five minutes of ExUnit test time because a test
can perform multiple verifications, each waiting for the bounded job budget.
This is a test scheduling allowance. Public per-target deadlines (including the
default deadline), Lean options, negative-proof checks and deliberate timeout
tests are unchanged. Queued time remains part of each public target's deadline.

## Profiling parameterized cases

Scenario setup labels the current process with its test and program parameter.
The profiler propagates that identity through Task caller ancestry; the formatter
also records ExUnit's parameters. Summary lookups include parameters, preventing
request counts or durations from different instances of the same test name from
being combined. Tests without parameters and older event streams retain their existing
identity format.

## Reproducible selected-suite comparison

The benchmark accepts `--test-files` with `--suite-only`. It validates a comma-
separated list of existing test files inside `test/` and records the selection in
metadata. For example:

```sh
ERL_FLAGS='+S 4:4' LEAN_NUM_THREADS=2 REDUCTION_BOUNDS_LEAN_JOBS=2 \
  mix reduction_bounds.bench --suite-only --seed 0 --max-cases 4 \
  --test-files test/reduction_bounds/port_completion_proof_test.exs,test/reduction_bounds/contract_workflow_test.exs,test/reduction_bounds/bound_transfer_test.exs \
  --suite-repetitions 1 --output _build/selected-parallel.json
```

Repeat separately with `--max-cases 1` and a different output file for a serial
reference using exactly the same source, fixtures, scenarios and assertions.
Both runs start with their own empty verification cache and repeat with the warm
cache in a fresh VM. They do not clear the normal build or its cache. Hold the
job budget, Lean threads and machine settings fixed. Measure ordinary runs rather
than enabling `--trace` or `--slowest`.

Use several seeds and concurrency settings for correctness validation. Compare
command wall time, memory, admitted jobs and cache flags. Per-test durations can
increase while cases wait for a job slot even when whole-suite throughput improves.
See [profiling and the job budget](job_budget.md) for timing and sampling limits.

The [recorded measurements](baselines/issue8-fixture-concurrency.md) include
a same-source serial/parallel comparison and two ordinary full-suite validations.

## Remaining independent proof families

The following additional modules now run asynchronously under the same per-VM
verification job budget:

| Module | Isolation audit |
| --- | --- |
| `ProtocolProofTest` | Builds request-local contracts, traces and proof strings; no fixture or environment mutation. |
| `ProtocolConditionsProofTest` | Builds request-local observations, sizes and bounds; altered evidence is a separate immutable proof value. |
| `ProtocolCostProofTest` | Builds request-local participant budgets and rules; no shared mutable model state. |
| `IntegerSizeProofTest` | Reads packaged Lean sources and generates one local proof per check; axiom audits remain intact. |
| `ExecutionComparisonTest` | Builds local contracts and proof declarations, retaining the bound audit before verification. |
| `StructBoundTest` | Reads the canonical bounded-counter module and immutable BEAM compiled once by `test_helper.exs`; never recompiles or purges it. |

All verification still uses the shared boundary and isolated one-shot runner
request environments. Logical Lean filenames and declaration names are not
shared writable files; artifact keys include the final source and dependencies.
All positive, changed-evidence, incorrect-bound and unfinished-proof assertions
are retained. No production Lean source or verification semantics changed.

Three Protocol-family loops that previously submitted independent proofs
sequentially are now eleven native parameterized cases: five protocol traces,
three condition traces and three cost traces. Each case has a stable scenario
identity in the profiler, matching ExUnit's parameter map. Scenario data has one
source of truth in each file's support module, shared by parameter selection and
proof construction. These eleven instances replace three monolithic tests,
adding eight reported tests without changing the inputs or verification count.
The selected six-file cohort has 40 tests and 47 runner invocations.

The loops inside integer-size tests still construct a single combined proof;
negative tests still check all their deliberately altered variants. They are not
split merely because they contain a `for` expression. Scenario-local proof
construction and checks remain ordered.

Protocol, integer-size and struct cases use the same five-minute ExUnit
scheduling allowance as the earlier asynchronous proof families. Execution
comparison retains its existing two-minute allowance. These are test-level
allowances for queueing and, where present, multiple requests. Public API target
deadlines, Lean options, the provisional default job budget of 2, and deliberate
timeout checks are unchanged. Raising runnable test counts can still exhaust a
public deadline; a timed-out configuration is a failure, not a speedup.

Environment/recorder mutation, worker/preparation unit coordination,
supervisor restart, and independent-VM publication tests remain synchronous.
Their shared state keeps them synchronous. Recheck promising job-budget settings
after changing the asynchronous workload; the interrupted earlier calibration
has not established an optimum.

For a same-source serial/parallel comparison, select these six files with
`--test-files`, hold the job budget and Lean threads fixed, and change only
`--max-cases 1` versus `--max-cases 4`. Use different outputs and isolated cold
caches. Validate another seed/case limit separately. Ordinary full-suite command
wall time, memory and failures remain the throughput and correctness checks;
parallel per-test duration sums overlap.

See the [remaining proof-family measurements](baselines/issue8-remaining-proof-concurrency.md)
for the controlled cohort comparison, isolation audit and full-suite validation.

See [heavy regression isolation](regression_isolation.md) for the separate
cache-policy, family, environment-mutation and independent-VM groups.
