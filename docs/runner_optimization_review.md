# Conditional runner optimization review

Runner reuse and cold dependency-graph scheduling are conditional follow-ups,
not prerequisites or automatic next milestones. The current backend remains
one-shot verification with dependency-ordered sequential files, shared checked
artifact reuse, coalesced preparation and the existing per-VM job budget.
Neither backend is selected by the diagnostic output below.

## What the pinned backend supports

The locked Lynx revision is `d74890ac7a446d57b762d0e4fcd3c848146b2ff6`.
Its public Elixir `Lynx.Commands.runner!/2` opens a Lake runner for one request,
collects through the terminal response, then closes the port. `verify!/3` uses
that wrapper. A reusable session API is not exposed by this revision's Elixir
commands. A supported session integration requires an upstream API/revision;
do not copy private port functions or patch fetched dependencies in place.

The Lean runner can read several requests and retain its immutable runtime
imports, but handles requests in order. Its verification loop processes each
file sequentially. Artifact maps and request environments are created anew for
each request. A persistent session would not automatically retain arbitrary
request-local declarations or eliminate per-module artifact loading.

Preparation coordination coalesces overlapping finalized shared keys. The owner
still executes its ordinary complete request; waiters do not occupy runner slots.
This is not a ready-node DAG scheduler, a separate shared-only build phase, or
parallel module elaboration within a request. Warm closures are still supplied
in deterministic dependency order to the runner.

Primary implementation references at the pinned revision:

- [Elixir one-shot commands](https://github.com/josevalim/lynx/blob/d74890ac7a446d57b762d0e4fcd3c848146b2ff6/lib/lynx/commands.ex)
- [Lean file loop and request lifecycle](https://github.com/josevalim/lynx/blob/d74890ac7a446d57b762d0e4fcd3c848146b2ff6/Lean/Lynx/Runner.lean)

## Correct timing attribution

The legacy `runner_non_module_wall_ms` subtracts module time from the entire
post-assembly request interval, including preparation coordination and admission
waiting. It is not a startup measurement. Increasing concurrency can inflate this
field even while command wall time decreases.

The new `optimization_evidence` section in benchmark summaries pairs each
completed request's actual `job.runner_call_wall_ms` with the module reports from
that same request. `paired_runner_non_module_wall_ms_sum` subtracts their module
times from the actual call, excluding preparation/admission waiting. It still
includes supervised dispatch, Lake/process startup, immutable runtime imports,
runtime fingerprint work, protocol handling and teardown outside the module loop.
It is not an isolated startup cost or a predicted saving from sessions.

Only numeric nonnegative timings are paired. Missing actual-call timing remains
unavailable; it is never reconstructed from the legacy interval. If module time
exceeds call time, that pair is flagged inconsistent and excluded from residual
sums rather than clamped into a plausible saving. Counts show the coverage of
known call times, valid pairs, missing pairs and inconsistent pairs. Concurrent
request sums overlap and are not a partition of suite wall time.

Per-module `time_ms` already includes imports, decoding/rendering, elaboration,
audits and artifact publication. It is not pure proof-elaboration time. Cached
modules still have loading costs. Empty theorem timing arrays do not prove that
proof work was free.

## Cache-state evidence

New event module reports include an observational `cacheable` flag from the final
input's key eligibility. This field is added only to event reports; public proof
results are unchanged. It identifies eligibility, not a guarantee of a hit.

The summary distinguishes fully cached accepted requests, accepted requests with
cacheable shared misses, target/other misses, work without cache keys or with caching bypassed, legacy
unknown policy, empty probes, and unsuccessful requests. Shared-module counters
include accepted requests only. An uncached report without policy information
cannot establish a cacheable cold miss: bypass and unknown-import cases also
recheck modules. Legacy hits remain recognizable as hits, but legacy miss policy
remains unknown. Module-time sums for eligible misses are diagnostic work, not
time that can be saved by parallel execution or an estimate of DAG speedup. Deliberately cold regression
cases can contribute misses too; specify whether the goal is test throughput or
application cold starts and measure representative workloads for that goal.

Negative proof reports, skipped dependents and unfinished requests are not
successful optimization samples. A suite may intentionally exercise them; use
its exit status and assertions to distinguish expected rejection from failure.

## Reviewing existing logs

```sh
mix reduction_bounds.assess docs/baselines/issue8-heavy-full.json \
  --output _build/heavy-optimization-review.json
```

This reads the adjacent `issue8-heavy-full_artifacts` event files and writes JSON
and Markdown. It never invokes Lean, starts sessions, changes configuration or
modifies the source benchmark. Saved absolute paths are not followed after a
report is moved. Missing adjacent events produce an incomplete report and a
nonzero task exit; choose a new output path when retrying. Existing outputs are
not overwritten. Complete means that event artifacts were available, not that
the benchmark passed or either optimization was approved.

For new evidence, use ordinary benchmark runs with a clean committed source,
fixed source/toolchain/seed/case/job/thread settings, isolated cold/warm caches,
repeated samples and CPU/memory recording. Run the existing empty and trivial
runner probes separately from representative named workflows. The empty request
skips immutable runtime imports; its call still includes Lake/process/protocol and
dispatch work. Separate probe differences are estimates, not exact initialization
breakdowns. Warm benchmark attempts use fresh VMs and cached artifacts, not
persistent runner sessions.

## Gates before implementation

| Candidate | Evidence and integration required |
| --- | --- |
| Runner reuse | Complete controlled job/thread calibration on the target workload; repeatable material call residuals after waiting is separated; upstream attribution or a supported session prototype that measures initialization savings; representative whole-command improvement at acceptable memory cost. |
| Cold DAG scheduling | Repeatable material cacheable shared misses on representative cold workloads; dependency and ready-frontier/critical-path measurements; account for extra runner launches and repeated imports; a supported preparation interface; lower cold command wall time under the same global job/thread budget and memory envelope. |

Choose practical acceptance targets before a prototype comparison. A large sum of
request residuals, many runner launches, many cold modules, or a static graph with
independent nodes does not by itself satisfy either gate. Current evidence does
not isolate startup, measure a cold critical path or demonstrate either backend's
throughput benefit. Keep the simpler backend while those requirements remain
unmet. The [reference-Mac comparison](baselines/issue8-mac-job-calibration.md)
now passes all four full-suite commands and supports an initial profile of
4 jobs with 2 Lean threads. It does not measure either proposed backend's
benefit. The portable fallback of 2 remains provisional on unmeasured machines;
public deadlines are unchanged. See [verification defaults](verification_defaults.md).

If a supported session prototype is justified, preserve separate environments,
artifact maps, target association, ordered results, diagnostics and transitive
axiom audits. One owner must drain each port through its terminal response. On
timeout, cancellation, crash or protocol failure, retire the worker and replace
it before assigning another request. Restart sessions when effective runtime or
toolchain identity changes. Validate success/failure in both orders, repeated
declaration names across requests, interruption, cleanup and shutdown.

A cold prototype can first evaluate the supported ordered-file verification API
with each node's complete checked dependency closure; request an upstream addition
only if that interface is insufficient.

A cold scheduler must retain cache invalidation and atomic publication, verified
source/callee replay, deterministic reports and failure propagation. Dependents
must not start before their prerequisites are checked; waiting must not consume
capacity needed by preparation. Preserve deadline scope and cancellation while
queued. Integrate only through supported Lynx interfaces and retain the current
one-shot path as a comparison until the alternative meets the gates.

The [recorded conditional review](baselines/issue8-conditional-runner-review.md)
includes legacy-log reassessment, new probes and native cache-policy validation.
