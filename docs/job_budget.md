# Profiling and the Lean job budget

All production verification goes through one per-VM job budget. The default is
**2 admitted jobs**, independent of ExUnit's `max_cases` and each API call's
`max_concurrency`. This stage does not change synchronous test modules to run
asynchronously, batch requests or introduce persistent Lean sessions.

Set the limit before starting the application:

```sh
REDUCTION_BOUNDS_LEAN_JOBS=2 mix test --seed 0 --max-cases 24
```

Alternatively set `config :reduction_bounds, :lean_jobs, 2`. The environment
variable takes precedence. The limit must be a positive integer; invalid values
fail application startup. Changes require restarting the application. Independent
OS processes have separate budgets; this is not a machine-wide resource limit.
Lean's own threads are additional concurrency. Start with job counts 1, 2 and 4
and explicit `LEAN_NUM_THREADS`, measuring memory and wall time before increasing
either. More jobs are not automatically faster on heterogeneous CPU cores.

## Admission, cancellation and recovery

Assembly and shared-preparation coordination happen before admission. A caller
waiting for another caller's shared dependency closure holds no job slot. A
preparation owner acquires a slot only when it can invoke the runner. The same
budget covers cached, uncached, embedded and raw verification requests.

Admitted work runs in a supervised task. The coordinator monitors both the
requesting process and its worker. Caller termination kills the worker, closing
its runner port. An occupied slot is retained until that worker terminates;
queued callers are monitored and cancelled callers cannot later start a runner.
Callback exceptions retain their original kind and reason and release capacity.
FIFO admission is independent of target result ordering.

Supervision stops old workers before restarting a failed budget coordinator,
avoiding a capacity reset while old jobs continue to run. Unexpected coordinator
or worker termination can fail affected requests; it does not turn a failed proof
into a successful result or retry an interrupted request silently.

The existing per-target task timeout includes assembly, shared preparation,
admission queueing and verification. Source analysis before those target tasks
retains its existing timeout behavior. A timeout while queued still returns the
same target-associated timeout error. Direct internal verification helpers have
no additional deadline; their caller can cancel them. Backend build work started
by a one-shot invocation uses that invocation's slot. The benchmark explicitly
builds the runner through Lynx's supported Lake API before measuring requests.

## Ordinary suite profiling

```sh
REDUCTION_BOUNDS_LEAN_JOBS=2 LEAN_NUM_THREADS=2 \
  mix reduction_bounds.bench --suite-only --seed 0 --max-cases 24 \
  --output _build/suite-profile.json
```

This prepares an isolated Mix build and runner, then measures the ordinary suite
with an empty verification cache. Add `--suite-repetitions 1` to run the same suite
and seed once more using the resulting warm cache. Every suite run is a fresh
VM. The JSON records source status, toolchains, concurrency and machine resources.
Use a clean committed source tree for published measurements. No ordinary build
or cache is deleted. For an existing build/cache, enable the event stream directly:

```sh
REDUCTION_BOUNDS_BENCH_EVENTS=/absolute/path/events.jsonl \
  REDUCTION_BOUNDS_LEAN_JOBS=2 mix test --seed 0 --max-cases 24
```

Choose a new event filename per run: event streams append. Direct `mix test`
produces events without the command-level CPU/memory report. The benchmark task
also produces a summary. `--slowest` and `--trace` remain separate diagnostic
tools; neither is enabled by the profiling formatter.

The extra formatter preserves configured formatters and records each test's
native duration, asynchronous flag, name and location. Summaries rank individual
tests and aggregate their durations by module. Test durations exclude module
setup, cleanup and loading, and sums across asynchronous cases can overlap.
The suite event retains ExUnit's native phase durations. Use command wall time
for throughput rather than adding request/test durations.

Source extraction and proof generation are timed at the public workflow's source
producer calls. Separate proof-input spans cover shared-source generation and
translation-input registration. Verification events distinguish assembly,
shared-preparation identity lookup/waiting, admitted job queueing, supervised
runner-call wall time, and individual module timings/cache flags. The remaining
runner-call overhead includes imports, artifact loading, process/Lake startup,
protocol and teardown; it is not a pure startup measurement.

On the current Elixir/OTP toolchain, process labels and Task caller ancestry
associate events with their originating ExUnit test, including supervised runner
tasks. Unlabelled/background processes and independent VMs may have no test
context. These are retained rather than assigned by timing guesses. Per-test
summaries attach completed request counts and source/proof-input timing sums.
Tests that intentionally disable or redirect event recording are absent from
request aggregates; their native test timings are still recorded.
A timed-out request can have a start without a completion event. Exceptions can
also finish a request without a normal module report.

`runner_started` counts observed calls entering the supported Lynx verification
API, including empty probes. `peak_active_jobs` is the largest admitted slot count
observed at those calls, not a count of every descendant OS process. Aggregate
queue durations cover admitted requests; cancelled waiting time can be absent.
Supervised dispatch overhead is included in runner-call wall time. These fields
are unavailable or incomplete in older report schemas. Schema 2 retains the
older timing fields for comparison.

## CPU and memory sampling

The command sampler reads process-tree RSS and cumulative CPU clocks every
100 ms using `ps`, with Linux and macOS clock formats supported. It sums the
largest observed CPU counter for each observed PID. Short-lived processes and
work after a process's final sample can be missed; Linux counters can have only
one-second precision. CPU values are sampled estimates, not exact accounting.
`sampled_tree_cpu_percent` divides sampled CPU time by command wall time:
100% represents one core and values can exceed 100%. It is not a percentage of
all available cores. RSS can count shared pages more than once. Unavailable
sampling is reported as `null`.

## Small concurrency experiment

```sh
REDUCTION_BOUNDS_LEAN_JOBS=2 LEAN_NUM_THREADS=1 \
  mix reduction_bounds.bench --no-suite --workloads concurrent_integer \
  --repetitions 3 --output _build/jobs-2.json
```

Repeat with limits 1 and 4, using separate output files. This workload prepares a
common integer theory and submits four independent targets concurrently through
the normal verification boundary. It tests the budget under load without changing
ExUnit fixture isolation. It is a synthetic concurrency probe, not a prediction
of full-suite speedup. Keep cache state, Lean threads and machine settings fixed.

The [recorded suite profile and job comparison](baselines/issue8-job-budget.md)
identify expensive tests and the measured memory/wall-time trade-off.
