# Heavy regression-test isolation

Heavy regression tests are scheduled according to the state they actually use.
Each cache-policy scenario retains its dependent request sequence; changing the
schedule does not replace checked Lean artifacts with remembered Elixir results.

| Group | Scheduling | State and isolation |
| --- | --- | --- |
| Proof-family comparisons | Five asynchronous parameter instances | Canonical immutable theories; named, reused, bypassed and embedded requests stay in order within each family. |
| Cache-policy regressions | Four asynchronous parameter instances | A fresh source identity per scenario isolates its shared theory and complete dependent closure from every other caller. |
| Preparation integration | Asynchronous module | Concurrent targets use a private shared-source identity; compiled-dependency checks write only inside the case's temporary directory. |
| Public mode comparison | Synchronous module | Changes the process-wide proof-mode environment variable and compiles/purges an owned fixture; restores state and cleans up. |
| Independent-VM publication | Synchronous module | Starts two concurrent child VMs, then a third warm reader; child budgets are separate from the parent's budget. |

## Cache-state scenarios

`ProofCacheTest` covers reuse, invalidation, invalid targets and invalid
shared sources. Each instance appends a fresh comment to its own copy of the
integer-size source. The final cache keys include that source and propagate
through its dependencies, so another instance or proof family cannot warm or
modify the keys on which its assertions depend. The module names and actual
Lean claims are retained; content identities provide isolation in the existing
atomic artifact store. No shared cache root is deleted or reconfigured.

The first request in each scenario must be fully uncached. Subsequent requests
verify shared reuse across distinct targets, target reuse, shared-only caching,
bypass behavior, changed sources/options and repeated rejection of invalid or
unfinished proofs. A distinct second target must remain uncached before its
own warm retry. Successful setup, invalidation and rejection checks remain in
scenario order. Fresh identities deliberately exercise cold preparation again
in each VM, including warm-suite repetitions; these regressions are not warm
application throughput benchmarks.

The five ordinary family comparisons share canonical sources where appropriate.
Each family still performs four requests in order: named, repeated named,
uncached named, then uncached embedded. Independent families can overlap through
the existing verification boundary and per-VM job budget. Preparation integration
uses unique keys and inspects only its own reports; it does not reset or restart
the global coordinator. The compiled-dependency test uses a private temporary
project path, never the actual runtime's compiled dependency files.

## Global state and child VMs

`ProofModeComparisonTest` remains synchronous because the public API comparison
changes `REDUCTION_BOUNDS_PROOF_MODE`. The previous value is restored in `after`;
its private fixture is purged/deleted on exit. Both size and cost claims, all
assumptions and audited theorem names are still compared across modes.

`ProofPublicationTest` remains synchronous because child VMs do not share the
parent's job budget. It builds the runner through Lynx's supported Lake API
before launching two child VMs. Each child has an explicit one-job budget, one
Lean thread and two BEAM schedulers. Thus the publication stage runs at most two
one-shot verification invocations concurrently; no parent proof work runs in
parallel during this synchronous test. This is a test arrangement, not a new
machine-wide limiter or a production default.

Both child Task results must match successful command results, exit with zero,
and return one nonempty set of accepted module reports. At least one publisher
must report uncached work, confirming that cold publication was exercised. The
third independent VM must then read entirely cached accepted artifacts. Failed
Task results can no longer be skipped by a pattern-filtering comprehension.
The existing 90-second child Task timeout and two-minute test timeout remain.

The cache/preparation scenarios use the existing five-minute asynchronous test
allowance for several queued requests. The preparation integration's one-minute
Task timeout, all public target deadlines, negative tests and production Lean
options are unchanged. Environment/recorder mutation, supervisor restart and
other stateful unit tests remain synchronous.

## Validation and measurement

The split preserves all 13 regression cases: five families, four cache policies,
two preparation/context checks, one public mode comparison and one multi-VM
publication case. It retains 49 verification calls, including the three child-VM
calls. Parent test durations include the child commands, but child verification
events may have no ExUnit context; do not assign them by timing guesses. Each
child reports its own one-job limit, and observed admission is not a count of all
OS descendants.

Use `mix reduction_bounds.bench --suite-only --test-files PATHS` with these five
files to compare the same source and assertions at ExUnit max cases 1 and 4:

- `test/reduction_bounds/proof_families_test.exs`
- `test/reduction_bounds/proof_cache_test.exs`
- `test/reduction_bounds/proof_preparation_integration_test.exs`
- `test/reduction_bounds/proof_mode_comparison_test.exs`
- `test/reduction_bounds/proof_publication_test.exs`

Hold the job budget, Lean threads, seed and cache policy fixed. Use isolated cold
caches and different output paths. Measure ordinary command wall time and memory;
per-test and request duration sums overlap. Validate another seed/case limit and
the full suite separately. A failed or timed-out run is not a successful speedup.
The default job limit remains a provisional 2; this split does not calibrate it
or introduce persistent runners.

See the [recorded regression measurements](baselines/issue8-heavy-regression-isolation.md)
for the controlled cohort comparison, resource samples and full-suite validation.
