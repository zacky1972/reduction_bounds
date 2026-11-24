# Verification baseline

Run the opt-in task from the project root with the locked dependencies and Lean
toolchain installed:

```sh
mix reduction_bounds.bench --output _build/baseline.json
```

The task selects the test environment so the circular-buffer dependency is
available. It compiles a new, disposable Mix build and measures integer analysis,
integer costs, bound transfer, list, circular-buffer, and Port workflows. It also runs the
ordinary full suite once, with a recorded seed and maximum concurrent case
count. Each representative workload has one cold verification-cache run and
three subsequent warm attempts, each in a fresh OS process. To shorten an exploratory run:

```sh
mix reduction_bounds.bench --no-suite --workloads integer_cost,list --repetitions 1
```

Other switches are `--max-cases N`, `--seed N`, and `--keep-workspace`. The JSON
report records the source revision/status and tracked diff digest, dependency
revisions, lock digest, Elixir/OTP/ERTS/Lean/Lake versions, machine resources,
selected environment settings, and concurrency. For a publishable baseline,
commit source changes first; a dirty checkout's status/diff is a diagnostic aid,
not a substitute for publishing all measured source.

Logs and per-request JSON lines are saved in a sibling directory ending in
`_artifacts`. The temporary build is removed unless `--keep-workspace` is set.
Only that invocation's verification-cache directory is cleared between cold
scenarios. The normal `_build` and its verification cache are not cleared.
Lean artifacts under the dependency's `.lake` directory may already exist:
their presence is recorded, and the preparation measurement must not be
described as a fresh Lean/toolchain installation. Dependency downloads and the
initial compilation needed to load this Mix task are outside the measured scope.

## Interpret the results

- Command `wall_ms` is the throughput measurement, including child VM/application
  startup and analysis/proof generation before the verification boundary.
  Request duration sums can overlap during concurrent suite tests and
  must not be substituted for command wall time.
- Request events separate assembly from the runner call and preserve module
  `time_ms`, `cached`, status, and available theorem timings. The runner's module
  durations cover rendering, imports, elaboration, auditing, and artifact writes.
- `runner_non_module_wall_ms` is the remaining runner-call wall time. It includes
  preparation coordination, Lake/process startup, shared-runtime initialization,
  protocol, and teardown.
  The pinned Lynx API cannot isolate these components individually. The
  `runner_empty` and `runner_runtime` workloads provide startup-only and trivial
  runtime-loading probes; differences between separate runs are estimates,
  rather than exact initialization timings.
- Empty theorem-timing arrays mean timings are unavailable (or no elaboration
  occurred on a cache hit), not that proof cost was zero.
- All packaged proof families reuse checked named theories and target modules.
  Ad-hoc raw proofs without shared theories remain uncached.
  Cold/warm labels describe the verification-cache lifecycle; inspect each
  module's `cached` flag rather than assuming a hit. Stage 1 deliberately disabled
  all verification caching, so its warm attempts had no hits.
- Memory is the largest 100 ms sample of summed RSS for the child process tree.
  Shared pages can be counted multiple times, short peaks can be missed, and
  `null` indicates unavailable sampling. It is not an exact OS high-water mark.
- Started requests without terminal events identify interruptions such as task
  timeouts. A failed proof may have a completed runner request containing error
  reports; request completion is not proof acceptance.

Use ordinary runs without `--trace` or `--slowest` for throughput comparisons.
`mix test --slowest 20` is useful for locating expensive tests but enables trace
mode and serializes cases. Hold machine settings and concurrency fixed when
comparing revisions. Do not infer a speedup from a single noisy run.

## Verification boundary

The internal verification boundary finalizes imports and cache keys before
invoking the existing Lynx runner. Production APIs and proof-test helpers use the
same boundary. Result/error formats, target ordering, and timeouts are retained.
Verification reports include the shared modules before
`Erlang.postlude`; every report must succeed for the request to be accepted.
Optional event recording is enabled only in benchmark child processes. It is
observational: an unavailable event destination cannot change verification.
All packaged proof families now use shared modules, including Core/struct rules,
normalization and execution, integer analysis and contracts, protocol/Port,
list/composed proofs, and buffer/periodic models. Existing namespaces and source
locations are retained. A supervised coordinator coalesces overlapping cold
preparation in one application. See [shared proof modules](shared_proofs.md)
for dependency handling, readiness, failure and cancellation behavior.
The pinned runner still processes its dependency-ordered inputs sequentially.

Keys cover the complete finalized module input, ordered dependency keys, and
effective Lean options. Lynx additionally partitions artifacts by Lean version,
compiled runtime hashes, and options. Unknown external imports disable caching
for their consumers and dependents because Lynx's runtime fingerprint does not
cover arbitrary compiled modules. Both shared modules and generated targets are
audited for transitive axiom dependencies before successful artifact publication.
Cached artifacts retain those checks; result maps are never accepted as evidence.

To bypass verification-cache reuse in application workflows:

```sh
REDUCTION_BOUNDS_PROOF_CACHE=off mix test
```

To compare the original concatenated-source implementation:

```sh
REDUCTION_BOUNDS_PROOF_MODE=embedded mix test
```

Use the same variables with `mix reduction_bounds.bench`. Setting
`REDUCTION_BOUNDS_PROOF_CACHE=shared` caches only shared theories and rechecks
all targets. Defaults are named shared modules and caching enabled. These
switches do not clear the caller's cache. Focused cache regression tests explicitly
exercise all modes regardless of these defaults. No persistent runner pool is added.

A recorded [stage 1 baseline](baselines/issue8-linux-otp29.md) includes the
measurement command, raw reports, and full-suite result.

The [integer pilot measurements](baselines/issue8-integer-cache.md) compare the
embedded path, shared-theory caching, and shared plus target caching on the same
source revision and machine.

See the [all-family reuse measurements](baselines/issue8-all-proofs.md) for
controlled embedded, shared-only and default-cache comparisons.
