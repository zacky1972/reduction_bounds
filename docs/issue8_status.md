# Issue 8 status

Updated 2026-11-24. The original issue describes the initial inspection at
`b17e195`; it is not a description of the current implementation. The successful
reference-Mac calibration measures clean source `6ff038cebf09969e38498957e83393193527ba6a`.

## Implemented and validated

- One verification boundary finalizes imports and dependency-aware artifact keys.
- Named shared modules and reusable generated models preserve kernel checking,
  transitive axiom audits, source/callee replay and negative-proof rejection.
- Shared preparation is coalesced by dependency closure and runtime identity;
  publication and cancellation retain their regression coverage.
- Per-VM admission bounds aggregate verification work independently of per-call
  concurrency and Lean's own threads.
- Immutable fixtures, private cache identities and parameterized cases permit
  audited independent tests to run asynchronously. Global mutation, coordinator
  restarts and independent-VM publication tests retain required serialization.
- Benchmark, calibration and assessment tasks retain cold/warm, settings,
  command-time, resource and request evidence without silently selecting defaults.

The [reference Mac comparison](baselines/issue8-mac-job-calibration.md) passes
all four 345-test suites, including negative and timeout coverage. Jobs 4 with
Lean threads 2 takes 339.609 seconds cold and 277.794 seconds warm, versus
535.565 and 420.160 seconds at jobs 2. This is 36.6% and 33.9% shorter command
time in one paired trial, with higher sampled memory use.

The [final validation record](baselines/issue8-final-validation.md) also records
a passing 345-test Linux run at seed 42 with jobs 4 and Lean threads 2, required
static checks and warning-free documentation generation. It is a regression run,
not another controlled performance comparison.

Earlier maintainer logs progressed from 304 tests at 918.7/762.8 seconds through
322 tests at 517.5/496.1 seconds, 336 tests at 467.2/465.1 then 401.1 seconds,
and 342 tests at 405.5 seconds. They show the development history, not a controlled
speedup ratio: revisions, test counts, seeds and effective settings differ.

## Retained policy

Named modules and eligible shared/target caches remain enabled. The initial
reference-Mac profile is 4 jobs and 2 Lean threads; the portable fallback remains
2 and Lean threads remain caller-controlled. The public target deadline remains
60,000 ms. Embedded and cache-bypass comparisons remain supported using the same
source providers. See [verification defaults](verification_defaults.md).

No persistent runner or cold DAG scheduler is introduced. The current backend
starts one runner per call and processes modules in dependency order. Existing
paired residuals exclude admission waiting but do not isolate startup, and miss
times do not establish a cold dependency critical path.

## Open work and issue disposition

Keep Issue 8 open for the original startup/import attribution criterion. The
baseline, cold/warm separation, artifact reuse/invalidation, bounded-concurrency
comparison, full-suite correctness and documented bottleneck criteria now have
recorded evidence. Repeating the reference profile with rotated order would
strengthen its recommendation; it is not a prerequisite for publishing this
single-trial result. Neither 2 nor 4 is a universal optimum.

Runner reuse and cold DAG scheduling remain conditional follow-ups under the
[optimization review](runner_optimization_review.md). Do not treat deferred
backends as implemented or infer their expected savings from aggregate residuals.

The maintainer has updated the [issue body](https://github.com/zacky1972/reduction_bounds/issues/8)
and posted the [measured policy comment](https://github.com/zacky1972/reduction_bounds/issues/8#issuecomment-7128848077).
The initial findings are preserved as history and the issue remains open for
startup/import attribution.
