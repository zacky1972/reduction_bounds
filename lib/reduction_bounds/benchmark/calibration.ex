# cspell:words rootname
defmodule ReductionBounds.Benchmark.Calibration do
  @moduledoc false

  @controls ~w(source_revision source_status tracked_diff_sha256 lockfile_sha256 dependencies
    elixir otp_version erts lean lake lean_toolchain system processors processors_available
    schedulers_online memory_total_bytes container_memory_max container_cpu_max suite_seed
    suite_max_cases suite_files suite_runs verification_cache_policy)

  @spec run(keyword()) :: map()
  def run(opts) do
    unless source_state()["source_status"] == "",
      do: Mix.raise("calibration requires a clean committed source tree")

    output = Path.expand(opts[:output])
    artifacts = Path.rootname(output) <> "_artifacts"

    if File.exists?(output) or File.exists?(artifacts),
      do: Mix.raise("calibration output already exists; choose a new output path")

    File.mkdir_p!(artifacts)
    entries = plan(opts, artifacts)
    report = %{schema_version: 1, status: :running, plan: entries, results: []}
    save(output, report)

    results =
      Enum.reduce(entries, [], fn entry, results ->
        Mix.shell().info("Calibrating trial #{entry.trial}, jobs #{entry.jobs}: #{entry.report}")
        {_, status} = execute(entry)

        result =
          Map.merge(entry, %{
            exit_status: status,
            benchmark: read_report(entry.report),
            source_after: source_state()
          })

        results = results ++ [result]
        save(output, %{report | results: results})
        results
      end)

    comparison = summarize(results)
    status = if comparison.comparable, do: :completed, else: :failed
    report = Map.merge(report, %{status: status, results: results, comparison: comparison})
    save(output, report)
    File.write!(Path.rootname(output) <> ".md", markdown(comparison))
    Mix.shell().info("Calibration report: #{output}")
    unless comparison.comparable, do: Mix.raise("calibration is not comparable; see #{output}")
    report
  end

  @spec plan(keyword(), String.t()) :: [map()]
  def plan(opts, artifacts) do
    for trial <- 1..opts[:trials], jobs <- rotate(opts[:jobs], trial - 1) do
      report = Path.join(artifacts, "trial-#{trial}-jobs-#{jobs}.json")

      args = [
        "reduction_bounds.bench",
        "--suite-only",
        "--seed",
        to_string(opts[:seed]),
        "--max-cases",
        to_string(opts[:max_cases]),
        "--suite-repetitions",
        to_string(opts[:suite_repetitions]),
        "--output",
        report
      ]

      args = if opts[:test_files], do: args ++ ["--test-files", opts[:test_files]], else: args

      %{
        trial: trial,
        jobs: jobs,
        report: report,
        log: Path.rootname(report) <> ".log",
        args: args,
        env: %{
          "MIX_ENV" => "test",
          "REDUCTION_BOUNDS_LEAN_JOBS" => to_string(jobs),
          "LEAN_NUM_THREADS" => to_string(opts[:lean_threads]),
          "REDUCTION_BOUNDS_PROOF_MODE" => "named",
          "REDUCTION_BOUNDS_PROOF_CACHE" => "on"
        }
      }
    end
  end

  defp rotate(values, offset) do
    {left, right} = Enum.split(values, rem(offset, length(values)))
    right ++ left
  end

  defp execute(entry) do
    File.open!(entry.log, [:write], fn log ->
      System.cmd("mix", entry.args,
        env: Map.to_list(entry.env),
        stderr_to_stdout: true,
        into: IO.stream(log, :line)
      )
    end)
  end

  defp read_report(path) do
    case File.read(path) do
      {:ok, contents} -> JSON.decode!(contents)
      {:error, _reason} -> nil
    end
  end

  defp source_state() do
    Map.new(
      [{"source_revision", ["rev-parse", "HEAD"]}, {"source_status", ["status", "--porcelain"]}],
      fn {key, args} ->
        case System.cmd("git", args, stderr_to_stdout: true) do
          {text, 0} -> {key, String.trim(text)}
          {_text, _status} -> Mix.raise("cannot inspect calibration source state")
        end
      end
    )
  end

  @spec summarize([map()]) :: map()
  def summarize(results) do
    issues = Enum.flat_map(results, &issues/1)
    fingerprints = for %{benchmark: %{"metadata" => meta}} <- results, do: controls(meta)
    counts = for %{benchmark: %{"runs" => runs}} <- results, run <- runs, do: test_count(run)

    issues =
      issues ++
        if(length(Enum.uniq(fingerprints)) != 1, do: ["controlled metadata differs"], else: []) ++
        if(length(Enum.uniq(counts)) != 1, do: ["test counts differ"], else: [])

    rows =
      for %{jobs: jobs, benchmark: %{"runs" => runs}} <- results,
          run <- runs,
          is_map(run["verification"]),
          do: {jobs, if(run["phase"] == "cold", do: "cold", else: "warm"), run}

    %{
      comparable: results != [] and issues == [],
      issues: Enum.uniq(issues),
      scope:
        if(Enum.any?(fingerprints, &(&1["suite_files"] != [])), do: "selected", else: "full"),
      measurements:
        rows
        |> Enum.group_by(fn {jobs, phase, _run} -> {jobs, phase} end, &elem(&1, 2))
        |> Enum.map(fn {{jobs, phase}, runs} -> measurement(jobs, phase, runs) end)
        |> Enum.sort_by(&{&1.jobs, &1.phase})
    }
  end

  defp controls(metadata) do
    environment = Map.delete(metadata["environment"], "REDUCTION_BOUNDS_LEAN_JOBS")
    metadata |> Map.take(@controls) |> Map.put("environment", environment)
  end

  defp issues(%{jobs: jobs, exit_status: status, benchmark: benchmark} = result)
       when is_map(benchmark) do
    metadata = benchmark["metadata"]
    runs = benchmark["runs"]

    checks = [
      {status == 0 and benchmark["status"] == "completed", "benchmark failed"},
      {metadata["source_status"] == "", "source tree was not clean"},
      {result.source_after == Map.take(metadata, ~w(source_revision source_status)),
       "source changed during measurement"},
      {metadata["global_lean_jobs"] == jobs, "effective job limit differs"},
      {length(runs) == metadata["suite_runs"], "suite runs are missing"},
      {Enum.map(runs, & &1["phase"]) == phases(metadata["suite_runs"]), "cache phases differ"},
      {Enum.all?(runs, &valid_run?(&1, jobs)), "suite failed or profiling is incomplete"}
    ]

    for {false, message} <- checks, do: "jobs #{jobs}: #{message}"
  end

  defp issues(%{jobs: jobs}), do: ["jobs #{jobs}: benchmark report missing"]

  defp phases(count) when count > 1, do: ["cold" | Enum.map(1..(count - 1), &"warm_#{&1}")]
  defp phases(_count), do: []

  defp valid_run?(run, jobs) do
    verification = run["verification"] || %{}
    peak = verification["peak_active_jobs"]

    run["exit_status"] == 0 and run["workload"] == "suite" and
      is_map(verification["suite"]) and test_count(run) > 0 and
      is_integer(peak) and peak > 0 and peak <= jobs
  end

  defp test_count(run), do: get_in(run, ["verification", "tests", "count"]) || 0

  defp measurement(jobs, phase, runs) do
    %{
      jobs: jobs,
      phase: phase,
      samples: length(runs),
      command_wall_ms_median: median(Enum.map(runs, & &1["wall_ms"])),
      command_wall_ms_min: runs |> Enum.map(& &1["wall_ms"]) |> Enum.min(),
      command_wall_ms_max: runs |> Enum.map(& &1["wall_ms"]) |> Enum.max(),
      sampled_peak_tree_rss_bytes_max: maximum(runs, & &1["sampled_peak_tree_rss_bytes"]),
      sampled_tree_cpu_percent_median: median(Enum.map(runs, & &1["sampled_tree_cpu_percent"])),
      peak_active_jobs: maximum(runs, & &1["verification"]["peak_active_jobs"]),
      job_queue_ms_sum_median: median(Enum.map(runs, & &1["verification"]["job_queue_ms_sum"])),
      coordination_wall_ms_sum_median:
        median(Enum.map(runs, & &1["verification"]["coordination_wall_ms_sum"])),
      runner_calls_started: Enum.map(runs, & &1["verification"]["runner_calls_started"]),
      cached_modules: Enum.map(runs, & &1["verification"]["cached_modules"]),
      failed_requests: Enum.map(runs, & &1["verification"]["failed_requests"]),
      incomplete_requests: Enum.map(runs, & &1["verification"]["incomplete_requests"]),
      tests: Enum.map(runs, &test_count/1)
    }
  end

  defp maximum(runs, fun),
    do: runs |> Enum.map(fun) |> Enum.reject(&is_nil/1) |> Enum.max(fn -> nil end)

  defp median(values) do
    case values |> Enum.reject(&is_nil/1) |> Enum.sort() do
      [] ->
        nil

      sorted ->
        middle = div(length(sorted), 2)

        if rem(length(sorted), 2) == 1,
          do: Enum.at(sorted, middle),
          else: (Enum.at(sorted, middle - 1) + Enum.at(sorted, middle)) / 2
    end
  end

  @spec markdown(map()) :: String.t()
  def markdown(comparison) do
    rows =
      Enum.map(comparison.measurements, fn row ->
        "| #{row.jobs} | #{row.phase} | #{row.samples} | #{seconds(row.command_wall_ms_median)} | " <>
          "#{gib(row.sampled_peak_tree_rss_bytes_max)} | #{row.peak_active_jobs} |"
      end)

    Enum.join(
      [
        "# Lean job-budget calibration",
        "",
        "Scope: #{comparison.scope} suite. Comparable: #{comparison.comparable}.",
        Enum.join(comparison.issues, "\n"),
        "",
        "| Jobs | Cache | Samples | Median command seconds | Maximum sampled RSS, GiB | Peak admitted jobs |",
        "| ---: | --- | ---: | ---: | ---: | ---: |",
        Enum.join(rows, "\n"),
        "",
        "Cold and warm samples are separate; every suite run uses a fresh VM. " <>
          "RSS may count shared pages repeatedly. CPU 100% represents one core. " <>
          "Queue and preparation sums overlap across requests and are not suite-time partitions. " <>
          "Expected negative/timeout request events are not suite failures. " <>
          "One trial is exploratory; repeat promising configurations before choosing defaults. " <>
          "No default is selected automatically.",
        ""
      ],
      "\n"
    )
  end

  defp seconds(value), do: :erlang.float_to_binary(value / 1000, decimals: 3)
  defp gib(nil), do: "unavailable"
  defp gib(value), do: :erlang.float_to_binary(value / 1_073_741_824, decimals: 2)

  defp save(path, report) do
    File.write!(path <> ".tmp", [JSON.encode!(report), "\n"])
    File.rename!(path <> ".tmp", path)
  end
end
