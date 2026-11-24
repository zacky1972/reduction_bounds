<!-- cspell:words uncacheable -->
# Issue 8: conditional runner optimization review

Measured source: `3c9edf7`, clean for both new benchmark commands. Remote branch
`8` was reviewed at `fdb0fceafacd0ed3f168e48b62330ff3ddc19f42`, with Issue 8's
conditional follow-up plan. Linux x86-64, Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0,
locked Lynx revision unchanged. Parent commands used `ERL_FLAGS='+S 4:4'`,
`LEAN_NUM_THREADS=2`, jobs 2, named modules and caching enabled. No tests or checks
ran concurrently with measurement. Runner preparation preceded measurement.

## Implementation and decision

The one-shot backend, dependency-ordered sequential module loop, preparation
coordinator, public proof reports, timeouts, axiom audits and defaults are
unchanged. No pool, reusable session or cold node scheduler is introduced.

Optional event reports now include final-input cache-key eligibility. Benchmark
summaries pair actual runner-call time with module times from the same completed
request. Missing timing remains unavailable; inconsistent pairs are counted and
excluded from residual estimates. New summaries separate accepted cacheable
shared misses, bypass/uncacheable work, legacy unknown policy, fully cached
requests, target/other misses, empty probes and rejected requests.

`mix reduction_bounds.assess` reprocesses adjacent JSONL artifacts into JSON and
Markdown without invoking Lean or modifying the original benchmark. It rejects
existing output paths and reports missing artifacts explicitly. A complete review
is not a passing benchmark, approval, backend selection or speedup claim.

**Decision: keep both optimizations conditional.** Actual-call residuals indicate
work outside per-module timing, but do not isolate startup or predict session
savings. Module miss times include loading/rendering/audits/publication; no cold
critical path or ready-frontier timing was measured. The pinned public Elixir API
provides one-shot calls, not a reusable session interface. Target-machine job/thread
calibration remains incomplete. Establish representative command-level benefits,
acceptable memory, supported integration and lifecycle/correctness coverage before
implementing either candidate. See the [review criteria](../runner_optimization_review.md).

## Existing full-suite evidence, reprocessed

The legacy review reads the prior heavy-regression full-suite events from the
adjacent stored artifacts. That historical suite passed 336 tests. This stage
does not rerun that full suite or relabel it as current-source validation.

There are 36 fully cached accepted requests with 79.819 seconds of aggregate
actual-call time and 30.215 seconds of paired residual. Those sums overlap across
concurrent requests and cannot be interpreted as whole-suite savings. The other
accepted group has unknown cache policy: 72 shared module misses cannot be
classified as cacheable cold misses from the old events alone. Metadata's default
cache mode is insufficient because individual regression requests override it.
The new reader retains that uncertainty rather than inferring a cold DAG benefit.

## New one-shot probes

All 16 commands succeeded: one cold and three warm attempts for each workload.
Each workload starts with an isolated empty verification cache; warm attempts
reuse its artifacts in fresh VMs. Dependency build artifacts and OS caches may
already be warm. Values are medians within each row, in seconds; medians of
different columns need not come from the same attempt.

| Workload | Cache phase | Samples | Command wall | Actual call | Paired call residual |
| --- | --- | ---: | ---: | ---: | ---: |
| `runner_empty` | cold | 1 | 0.680 | 0.180 | 0.180 |
| `runner_empty` | warm | 3 | 0.741 | 0.173 | 0.173 |
| `runner_runtime` | cold | 1 | 2.248 | 1.389 | 1.384 |
| `runner_runtime` | warm | 3 | 1.503 | 0.683 | 0.678 |
| `integer_cost` | cold | 1 | 9.854 | 8.967 | 0.664 |
| `integer_cost` | warm | 3 | 2.780 | 1.938 | 0.656 |
| `port_source` | cold | 1 | 13.428 | 12.437 | 0.641 |
| `port_source` | warm | 3 | 2.858 | 2.000 | 0.709 |

Empty requests skip immutable runtime imports. Trivial raw proofs remain outside
the shared-module cache. Integer and Port source warm requests are fully cached;
their cold requests have eligible shared misses. The residual excludes preparation
and admission waiting but includes dispatch, Lake/process startup, immutable
runtime loading, protocol and teardown outside module reports. Separate probe
differences are not exact startup measurements. These probes do not compare
one-shot execution with a persistent backend, and supply no DAG scheduling result.

## Native cache-policy validation

The existing 13-case heavy regression cohort passed at seed 42, ExUnit max cases
4, parent jobs 2, in **121.557 seconds command wall time**. It retained 49 runner
calls, including three child VMs with their existing one-job limits. All native
positive, negative, cache-state and publication assertions passed.

Among accepted requests, evidence reports 51 shared cache hits, 43 eligible shared
misses (68.506 seconds of aggregate reported module time), and 30 misses without
cache eligibility. Unknown policy misses are zero in the new events. This is
regression coverage with deliberately cold sources and bypass modes, not an
application cold-start prediction. Failed/unfinished proof cases remain separate
from accepted optimization samples. Per-module time is not pure elaboration.

Reprocessing each new benchmark through the assessment task reproduced the
embedded `optimization_evidence` summaries exactly. All observed completed timing
pairs were valid, with no missing or inconsistent timing pairs. The old and new
cache-state distinctions are diagnostic evidence, not a performance recommendation.

## Validation and scope

- 33 focused tests passed: timing attribution, missing/inconsistent timing,
  bypass/unknown policy, artifact relocation, overwrite refusal, public report
  equivalence, error recording, queued deadlines, cancellation, preparation and
  calibration regressions.
- The native 13-case cache cohort passed with all proof modes and rejections.
- All 16 workload commands passed.
- `mix check` and `mix docs --warnings-as-errors` passed before measurement;
  final documentation, formatting and spelling checks cover this report.

Six added evidence/reader tests increase the full-suite inventory from 336 to 342.
The full 342-test suite was not rerun in this instrumentation/documentation stage.
The native backend invocation and ordinary unmeasured path are unchanged; validation
focuses on measurement semantics and the cache/verification boundary. No default
job count, public deadline or production proof was changed.

## Evidence and reproduction

```sh
REDUCTION_BOUNDS_LEAN_JOBS=2 LEAN_NUM_THREADS=2 \
  mix reduction_bounds.bench --no-suite \
  --workloads runner_empty,runner_runtime,integer_cost,port_source \
  --repetitions 3 --output _build/conditional-probes.json
```

Use the five heavy-regression files listed in the isolation guide with
`--suite-only --seed 42 --max-cases 4` for the native cohort. Run commands separately
with new output paths. Assessment reads a benchmark and its matching adjacent
`_artifacts` directory; it does not build or run Lean.

- [New probe benchmark](issue8-conditional-probes.json)
- [Native cache cohort](issue8-conditional-cache-cohort.json)
- [Legacy full-suite assessment](issue8-conditional-legacy-review.json)
- [Probe assessment](issue8-conditional-probe-review.json)
- [Cache assessment](issue8-conditional-cache-review.json)

Assessment JSON files have adjacent Markdown tables. Benchmark JSON files have
adjacent logs and JSONL events. Absolute paths identify the original workspace;
use the adjacent artifacts after relocating the checkout.

[Focused tests](issue8-conditional-validation_artifacts/focused.log),
[static checks](issue8-conditional-validation_artifacts/check.log),
[initial documentation](issue8-conditional-validation_artifacts/docs.log),
[command log](issue8-conditional-validation_artifacts/commands.log).
