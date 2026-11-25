# Test Performance Calibration

Use the existing calibration task to choose Lean job and thread settings for
`mix test` on your machine. This guide turns the Issue #8 workflow into a
repeatable procedure. It changes no proof, test assertion or production default.
Run it in the ReductionBounds repository, after [Getting Started](getting_started.md).

## Understand the independent limits

| Control | Meaning | How to set it |
| --- | --- | --- |
| `REDUCTION_BOUNDS_LEAN_JOBS` | Aggregate admitted verification jobs within one BEAM VM | Positive integer before application startup; fallback is 2 |
| `LEAN_NUM_THREADS` | Worker threads available to each Lean invocation | Positive integer in the parent environment; the library sets no default |
| `max_concurrency` | Target concurrency inside one public API call | API option; still constrained by the per-VM budget |
| ExUnit `--max-cases` | Concurrent asynchronous test cases | `mix test` option; not the Lean process/thread count |

The fallback of two jobs is not imposed by Lean, Lynx, RAM or CPU core count,
and is not a proven optimum. A reference M2 Max comparison supported an initial
four-job/two-thread profile for its measured workload. That is an example to
retest, not a universal hardware rule. Independent OS processes have independent
job budgets; the library does not impose a machine-wide cap.

Increasing jobs can increase memory use and contention. Keep Lean threads fixed
while comparing job budgets, then investigate thread counts separately. A rough
jobs-times-threads product is not an exact OS process count or a throughput law.

## 1. Prepare a stable measurement

Use a clean committed checkout with dependencies fetched and the required Lean
toolchain installed. Complete any edits and normal correctness checks first.

```sh
git status --short
mix deps.get
export ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)"
elan toolchain install "$ELAN_TOOLCHAIN"
lean --version
lake --version
```

`git status --short` must be empty before calibration. The task rejects tracked
changes and untracked files, including documentation edits or example source
files. Commit intentional work or use a separate clean checkout; do not remove
files simply to bypass the check. Outputs under the ignored `_build/` directory
avoid dirtying the checkout. Dependency commands must not leave a changed lockfile.

Record CPU/core configuration, memory, OS, power/thermal conditions and relevant
background activity. Keep the checkout, lockfile, toolchains, BEAM scheduler flags
(such as `ERL_FLAGS`), seed, case limit and other environment controls constant.
Do not edit the checkout, build docs, run another suite or run another calibration
while measuring. Full-suite runs can take several minutes each.

## 2. Make an exploratory job comparison

The following shell commands work in Bash and zsh:

```sh
report="_build/lean-jobs-$(date +%Y%m%d-%H%M%S).json"
mix reduction_bounds.calibrate \
  --jobs 2,4 \
  --lean-threads 2 \
  --seed 0 \
  --max-cases 24 \
  --suite-repetitions 1 \
  --trials 1 \
  --output "$report"
```

This runs **four full-suite commands**: cold and warm for jobs 2, then cold and
warm for jobs 4. `--suite-repetitions 1` means one warm run in addition to the
cold run. Each suite command starts a fresh VM. Configurations execute
sequentially, with isolated Mix builds and verification caches; runner preparation
is performed before timed suite runs. Cold/warm describe verification artifacts,
not a cold machine or a fresh dependency installation. The normal project cache
is not cleared.

The task sets jobs, Lean threads, named proof mode and shared/target caching in
child environments. It does not change your shell's environment. It checks source
state between configurations and compares controlled metadata. Other environment
settings are inherited, so use the same shell configuration across experiments.
Use `--jobs 1,2,4` if a serial reference is useful; that is six suite commands per
trial with one warm repetition.

To see all supported options:

```sh
mix help reduction_bounds.calibrate
```

## 3. Inspect validity before speed

The task writes the requested JSON, an adjacent Markdown summary and an adjacent
`_artifacts/` directory with per-configuration JSON, logs and event streams.

```sh
cat "${report%.json}.md"
```

Only compare successful reports with `Scope: full suite. Comparable: true.`
Check that every suite passed, the test counts agree, profiling is complete and
the observed admitted jobs respect the requested limits. Keep cold and warm
results separate. Preserve the JSON and all adjacent artifacts together when
sharing results; some assessments use adjacent event files.

| Report outcome | Action |
| --- | --- |
| `calibration requires a clean committed source tree` | Resolve the source state, then begin a new experiment |
| `calibration output already exists` | Choose a new timestamped path; do not overwrite an earlier measurement |
| `benchmark failed` or suite failure | Read that configuration's `.log` and its suite logs; diagnose the failing test before comparing times |
| `suite failed or profiling is incomplete` | Check the suite result and event completion; a short failed run is not a speedup |
| `controlled metadata differs` or test counts differ | Restore comparable source/settings and rerun the configurations |
| Missing CPU/RSS samples | Treat those measurements as unavailable, not zero |

For example, an `:enoent` for a packaged Lean resource is a build/resource
failure, not evidence that a lower job limit is faster. A task-stream timeout is
a failing integration test, not an admissible sample to discard silently. Keep
failed evidence and rerun after a justified fix on the same source for all
configurations. Do not increase public deadlines or weaken assertions to obtain
a favorable calibration.

Expected negative-proof and timeout tests can emit failed request events while
the suite passes. Distinguish those from actual ExUnit failures. An interrupted
experiment retains checkpoints but does not automatically resume; choose a new
output path for another invocation.

## 4. Repeat promising configurations

One paired trial is exploratory. Repeat before choosing a lasting profile:

```sh
report="_build/lean-jobs-repeat-$(date +%Y%m%d-%H%M%S).json"
mix reduction_bounds.calibrate \
  --jobs 2,4 --lean-threads 2 --seed 0 --max-cases 24 \
  --suite-repetitions 1 --trials 2 --output "$report"
```

This is eight full-suite commands. Trials rotate the configuration order and
start with fresh isolated caches. An extra `--suite-repetitions 2` adds another
warm run per configuration per trial; it does not add another cold run.
Compare command wall-time medians, variation, memory use, timeouts and failures
for both cache states. The task selects no default automatically.

After holding jobs fixed through this comparison, a separate exploratory
invocation can compare another Lean thread setting, for example
`--jobs 2,4 --lean-threads 1` with a new output path. Each calibration invocation
still requires at least two distinct job limits. Hold the remaining controls
fixed and compare only matching job rows across thread experiments.

RSS is a 100 ms sampled process-tree sum and can count shared pages repeatedly.
CPU 100% means one core, not the entire machine. Per-request queue/preparation
sums overlap across requests; do not add them as partitions of suite wall time.
Runner-call residuals include imports, artifact loading, protocol and teardown,
not just startup. See [measurement details](job_budget.md#cpu-and-memory-sampling).

For faster exploration, `--test-files` accepts comma-separated repository test
paths. A selected cohort does not establish a whole-suite profile:

```sh
mix reduction_bounds.calibrate --jobs 2,4 --lean-threads 2 \
  --seed 0 --max-cases 24 --suite-repetitions 1 --trials 1 \
  --test-files test/reduction_bounds/contract_workflow_test.exs,test/reduction_bounds/bound_transfer_test.exs \
  --output "_build/lean-jobs-selected-$(date +%Y%m%d-%H%M%S).json"
```

## 5. Apply the chosen profile to ordinary tests

If your measurements support four jobs and two Lean threads, apply both before
starting Mix:

```sh
REDUCTION_BOUNDS_LEAN_JOBS=4 LEAN_NUM_THREADS=2 \
  mix test --seed 0 --max-cases 24
```

To retain those settings for subsequent commands in the current shell:

```sh
export REDUCTION_BOUNDS_LEAN_JOBS=4
export LEAN_NUM_THREADS=2
mix test
```

Replace 4 and 2 with your measured choice. The second `mix test` uses ExUnit's
ordinary seed/case settings unless supplied; it is not the controlled calibration
command. Set the variables before `iex -S mix` too if running the
[Case Studies](case_studies.md) interactively. Changing the job environment variable
inside an already running application does not resize the budget; restart it.
For one command, prefix assignments affect only that invocation. `export` affects
future children of the current shell. To persist a profile across shell sessions,
put the exports in the appropriate shell startup file only after validation;
recalibration may require revising them.

Restore the ordinary environment in the current shell with:

```sh
unset REDUCTION_BOUNDS_LEAN_JOBS
unset LEAN_NUM_THREADS
```

Unset jobs falls back to application configuration (if provided) or two jobs.
Unset threads returns control to Lean's own behavior. Neither operation changes
an already running VM. Test counts and timing can change as new proof families
are added, so recalibrate after significant source, toolchain or test-concurrency
changes. Keep measured settings and raw reports with your experiment record.

## Deeper references

- [Calibration task and validity rules](job_calibration.md).
- [Effective defaults and override precedence](verification_defaults.md).
- [Profiling events and admission behavior](job_budget.md).
- [Benchmarking and cache-policy comparisons](benchmarking.md).
- [Conditional runner optimizations](runner_optimization_review.md).
