# Verification baseline

Run the opt-in task from the project root with the locked dependencies and Lean
toolchain installed:

```sh
mix reduction_bounds.bench --output _build/baseline.json
```

The task selects the test environment so the circular-buffer dependency is
available. It compiles a new, disposable Mix build and measures integer-cost,
bound-transfer, list, circular-buffer, and Port workflows. It also runs the
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
  Lake/process startup, shared-runtime initialization, protocol, and teardown.
  The pinned Lynx API cannot isolate these components individually. The
  `runner_empty` and `runner_runtime` workloads provide startup-only and trivial
  runtime-loading probes; differences between separate runs are estimates,
  rather than exact initialization timings.
- Empty theorem-timing arrays mean timings are unavailable (or no elaboration
  occurred on a cache hit), not that proof cost was zero.
- The current boundary deliberately retains `cache: false`. Consequently, warm
  attempts still verify proofs and are expected to report no verification-cache
  hits. Cold/warm labels describe the experiment's cache lifecycle, not an
  assumed backend optimization.
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

The internal verification boundary assembles translations with
caching disabled, finalizes additional imports, and invokes the existing Lynx
runner. Production APIs and proof-test helpers use the same boundary; the public
return values, ordering, axiom audits, errors, and timeouts remain unchanged.
Optional event recording is enabled only in benchmark child processes. It is
observational: an unavailable event destination cannot change verification.
This stage adds neither shared-module caching nor a persistent runner pool.

A recorded [stage 1 baseline](baselines/issue8-linux-otp29.md) includes the
measurement command, raw reports, and full-suite result.
