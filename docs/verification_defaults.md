# Verification defaults and measurement status

The retained defaults are named shared modules with shared and target artifact
caching. The job limit of **2 is a provisional fallback**, not a measured optimum
or a restriction imposed by Lean, Lynx or the hardware. The reference M2 Max
now has a successful controlled comparison supporting an initial recommendation
of **4 jobs with 2 Lean threads**. This policy review changes no runtime default,
proof or public deadline.

## Effective settings and overrides

| Setting | Retained behavior | Override and scope |
| --- | --- | --- |
| Shared module representation | Named modules | `REDUCTION_BOUNDS_PROOF_MODE=embedded` compares the original postlude representation. |
| Artifact reuse | Shared and target modules, where keys are eligible | `REDUCTION_BOUNDS_PROOF_CACHE=shared` caches theories only; `off` rechecks every module. |
| Aggregate verification admission | 2 jobs per VM, provisional | Set `REDUCTION_BOUNDS_LEAN_JOBS` before application startup, or application configuration `:lean_jobs`; the environment variable takes precedence. |
| Per-call target concurrency | 2 | Public `max_concurrency` is a per-call upper bound, additionally constrained by the VM job budget. |
| Public target deadline | 60,000 ms | Public `timeout` includes assembly, preparation waiting, admission and verification; existing validation rules apply. |
| Lean options | Empty option list unless supplied | Public `lean_options` affect elaboration and cache keys. |
| Lean worker threads | Not set by this library | Set `LEAN_NUM_THREADS` explicitly for a controlled comparison; the benchmark examples use 2, not a new production default. |
| ExUnit case count | Chosen by ExUnit or the caller | `mix test --max-cases N` controls test cases, not the number of Lean jobs or threads. |
| Runner lifecycle | One-shot calls with sequential dependency-ordered modules | Reusable sessions and cold DAG scheduling remain conditional follow-ups. |

Invalid job-limit values fail startup; changing the limit requires an application
restart. Different OS processes have different budgets. Independent-VM tests use
explicit child limits and run in the synchronous test phase. Neither core count
nor available memory alone determines an optimal job budget.

## Evidence behind the retained policy

Named modules share kernel-checked artifacts across different targets. Finalized
keys include complete sources, imports/dependencies, options and diagnostic
origins; Lynx additionally partitions by Lean/runtime identity. Unknown external
compiled imports disable caching for their consumers and dependents. Every
request still checks matching artifacts through the runner and retains transitive
axiom audits, source/callee replay and negative-proof rejection. Previously
returned Elixir maps are not proof evidence.

Reuse helps representative warm Port-source, contract and integer workflows.
The [all-family comparison](baselines/issue8-all-proofs.md) also records slower
small composed, buffer-sequence and periodic examples, and slower cold samples.
The default is a consistent reuse policy, not a universal fastest setting.
Measure representative workloads when startup/import costs dominate.

The controlled scheduling cohorts show shorter ordinary command wall times on
Linux while retaining the same verification calls and assertions. Those are
selected cohorts, not a claim about a whole-suite or Mac percentage. Source and
fixture isolation were audited before enabling asynchronous execution. Global
mutation, restart and independent-VM cases retain the required serialization.

The current application does not contain duplicate maintained copies of shared
Lean theories. Named and embedded assembly derive from the same packaged files
and source providers. Keep the embedded and cache-bypass controls as supported
diagnostic/comparison paths: mixed workload measurements still make them useful.
Removing them merely to end a migration would discard evidence and audit tools.

## Reference Mac configuration

The [M2 Max calibration](baselines/issue8-mac-job-calibration.md) passed all 345
tests in each of four full-suite runs, at the same clean revision, seed and case
limit. Jobs 4 reduced command wall time by 36.6% cold and 33.9% warm relative to
jobs 2, with maximum sampled process-tree RSS rising from about 1.99 GiB to
3.76 GiB. Use this explicitly selected profile on that reference machine:

```sh
REDUCTION_BOUNDS_LEAN_JOBS=4 LEAN_NUM_THREADS=2 mix test
```

To reproduce the test scheduling controls, also pass `--seed 0 --max-cases 24`.
Both variables must be set for this measured profile; leaving Lean threads
unspecified is a different configuration. This is an initial machine-specific
recommendation from one paired trial, not a global optimum or a portable default.
Repeat with rotated configuration order before making a stronger claim.

## What the measurements do not finalize

The earlier Linux calibration was interrupted, and jobs 2 with cold caches and
max_cases 24 had two public API deadline failures on that earlier source. Those
results remain historical unsuccessful configurations. The later ordinary Mac
logs did not record effective Lean job/thread settings or controlled cache state.
The new controlled Mac comparison supplies that missing evidence for its exact
revision and settings; it does not turn the historical runs into controlled data.

Retain the fallback of 2 for compatibility on unmeasured machines. No portable
adaptive policy or cross-machine optimum has been established. Set explicit
limits for the target workload and measure both throughput and memory. The Mac
comparison preserves the public 60,000 ms deadline; only an unrelated integration
test's nested stream limit was removed, retaining its ExUnit 300-second bound.

The paired actual-call residual excludes preparation/admission waiting but is
not isolated startup. Startup/runtime initialization attribution and cold
critical-path/frontier timing remain incomplete. The
[conditional optimization review](runner_optimization_review.md) records the
gates before adding a reusable backend or a cold scheduler.

## Repeating the controlled comparison

On the target Mac, use a clean committed checkout and a new output path:

```sh
mix reduction_bounds.calibrate --jobs 2,4 --lean-threads 2 \
  --seed 0 --max-cases 24 --suite-repetitions 1 --trials 1 \
  --output _build/mac-jobs2-vs4.json
```

This is four whole-suite executions: cold and warm at each limit. It can take
many minutes. Run one calibration at a time with other machine activity recorded.
Repeat promising configurations with `--trials 2` and a new output path; trials
rotate configuration order and each begins with a fresh cache. Compare threads
only after holding them fixed for the job comparison. Add jobs 1 as a serial
reference if useful. No task changes production defaults automatically.

Record command wall time, RSS/CPU samples, waits, effective settings, cache hits,
failures and timeouts. Missing/inconsistent results remain incomplete, and a
failed run is not a successful speedup. See [calibration](job_calibration.md) for
report validity and [benchmarking](benchmarking.md) for measurement scope.

## Issue status

The [Issue 8 status record](issue8_status.md) separates implemented work,
validation evidence, provisional policy and outstanding acceptance criteria.
The proposed GitHub update keeps the issue open for startup attribution;
optional backends are deferred rather than claimed as delivered.
