# Calibrating the Lean job budget

The global default of **2** is provisional. It is not a restriction imposed by
Lean or the hardware, and copying the old per-call limit does not preserve the
previous aggregate concurrency. Choose a job budget together with Lean's thread
count from measurements on the target machine. Linux results do not establish
the best setting for an M2 Max.

## Controlled sequential comparison

Start with a clean committed checkout and a new output path:

```sh
mix reduction_bounds.calibrate --jobs 2,4,1 --lean-threads 2 \
  --seed 0 --max-cases 24 --suite-repetitions 1 --trials 1 \
  --output _build/job-calibration.json
```

This runs the existing ordinary-suite benchmark separately for jobs 2, 4 and 1.
The configurations run sequentially. Each has its own isolated Mix build and
verification cache, a separate runner build before measurement, one cold suite
run, and the requested number of warm repetitions. Each suite run uses a fresh
VM; warm repetitions reuse only the corresponding configuration's artifacts.
Dependency Lean build artifacts may already exist. No normal cache is cleared.

The task sets `REDUCTION_BOUNDS_LEAN_JOBS`, `LEAN_NUM_THREADS`, named proofs and
artifact caching explicitly in child environments without changing the parent's
environment. Other settings, including BEAM scheduler flags, are inherited and
recorded. Keep them fixed, avoid simultaneous measurements, and record other
machine activity. The task cannot control thermal conditions, background work,
or heterogeneous-core placement.

For example, use `--jobs 2,4 --trials 2` and a new output path to repeat promising
configurations. Trials start with fresh isolated caches and rotate the supplied
job order. `--suite-repetitions 2` adds a second warm attempt in each trial;
it does not repeat the cold attempt. Compare a small set of Lean thread counts
in separate invocations only after comparing jobs with a fixed thread count.

A selected cohort is also supported:

```sh
mix reduction_bounds.calibrate --jobs 2,4 --lean-threads 2 \
  --test-files test/reduction_bounds/contract_workflow_test.exs,test/reduction_bounds/bound_transfer_test.exs \
  --output _build/selected-job-calibration.json
```

Selected-suite reports are labelled accordingly. They are useful for quick
experiments but cannot establish a full-suite default.

## Reports and validity

The output JSON checkpoints the plan and completed configurations. The adjacent
Markdown file shows cold and warm medians separately, sample counts and memory.
The `_artifacts` directory contains each benchmark JSON, command log, suite logs
and per-request events. Avoid overwriting these paths; choose a new output path
for another experiment. Interrupted experiments retain completed checkpoints;
there is no automatic resume or silent reuse of an earlier run.

A comparison is invalid if a benchmark/suite fails, required suite profiling is
missing, observed admission exceeds its configured limit, cold/warm phases are
missing, test counts differ, or controlled metadata differs. Controls include
source revision and cleanliness, lockfile/dependencies, toolchains, cache policy,
Lean threads, scheduler environment, machine resources, seed, case limit and
selected files. Source state is checked before the experiment and after each
configuration, as well as recorded at benchmark startup. Do not edit the checkout
or run other checks during timing measurements.

Failures remain in the report and make the task exit unsuccessfully. Intentional
negative proofs and timeout checks may produce failed or unfinished request
events in a *passing* suite; these counts are retained without treating them as
suite failures. No test or public target deadlines are increased by calibration.
A limit that causes real timeouts under the chosen case count is an unsuccessful
configuration, even if its reported elapsed time is shorter.

## Interpreting results

Use command wall time for throughput. Report medians and ranges across repeated
trials, sampled process-tree RSS, CPU samples, observed jobs, admission and
preparation waits, cache hits and runner counts. Missing CPU/RSS samples remain
unavailable rather than becoming zero. CPU 100% represents one core; RSS may
count shared pages repeatedly. Request duration and waiting sums overlap and
must not be added as a partition of suite wall time.

`runner_non_module_wall_ms` includes preparation/admission waiting as well as
runner-related overhead. Use `job.runner_call_wall_ms` to isolate the runner call
from those waits. That call still includes import/artifact loading, protocol and
teardown costs: its non-module remainder is not a pure startup measurement.

One trial is exploratory. Repeat promising configurations before documenting a
machine-specific recommendation or changing the portable default. Consider both
cold and warm workloads, memory and deadline failures, not only the fastest warm
sample. The task does not change configuration defaults automatically. Recheck
promising settings after expanding asynchronous tests, since that changes the
workload presented to the budget.
