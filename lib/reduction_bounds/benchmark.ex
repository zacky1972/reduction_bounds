# cspell:words rootname
defmodule ReductionBounds.Benchmark do
  @moduledoc false

  alias Mix.Dep.Lock

  alias ReductionBounds.Benchmark.Command

  @spec run(keyword()) :: map()
  def run(opts) do
    output = Path.expand(Keyword.fetch!(opts, :output))
    opts = Keyword.put(opts, :output, output)
    artifacts = Path.rootname(output) <> "_artifacts"
    File.mkdir_p!(artifacts)

    workspace =
      Path.join(
        System.tmp_dir!(),
        "reduction-bounds-bench-#{Base.url_encode64(:crypto.strong_rand_bytes(12), padding: false)}"
      )

    File.mkdir!(workspace)
    build = Path.join(workspace, "build")
    env = [{"MIX_ENV", "test"}, {"MIX_BUILD_PATH", build}]
    metadata = metadata(opts, workspace)

    try do
      Mix.shell().info("Preparing an isolated Mix build (logs: #{artifacts})")
      preparation = Command.run("mix", ["compile"], env, Path.join(artifacts, "prepare.log"))

      report = %{
        schema_version: 1,
        metadata: metadata,
        preparation: preparation,
        runs: [],
        status: if(preparation.exit_status == 0, do: :running, else: :failed)
      }

      write_report(output, report)

      if preparation.exit_status != 0,
        do: Mix.raise("benchmark preparation failed; see #{preparation.log}")

      runs = workloads(opts, env, build, artifacts) ++ suite(opts, env, build, artifacts)

      report = %{
        report
        | runs: runs,
          status: if(Enum.all?(runs, &(&1.exit_status == 0)), do: :completed, else: :failed)
      }

      write_report(output, report)
      Mix.shell().info("Benchmark report: #{output}")

      if Enum.any?(runs, &(&1.exit_status != 0)),
        do: Mix.raise("a benchmark failed; see #{output}")

      report
    after
      unless opts[:keep_workspace], do: File.rm_rf!(workspace)
    end
  end

  @spec summarize([map()]) :: map()
  def summarize(events) do
    completed = Enum.filter(events, &(&1["event"] == "completed"))
    reports = Enum.flat_map(completed, & &1["reports"])
    terminal = Enum.count(events, &(&1["event"] in ["completed", "failed"]))

    %{
      started_requests: Enum.count(events, &(&1["event"] == "started")),
      completed_requests: length(completed),
      failed_requests: Enum.count(events, &(&1["event"] == "failed")),
      incomplete_requests: Enum.count(events, &(&1["event"] == "started")) - terminal,
      assembly_ms: Enum.sum(Enum.map(completed, & &1["assembly_ms"])),
      runner_wall_ms_sum: Enum.sum(Enum.map(completed, & &1["runner_wall_ms"])),
      runner_non_module_wall_ms_sum:
        Enum.sum(Enum.map(completed, & &1["runner_non_module_wall_ms"])),
      cached_modules: Enum.count(reports, & &1["cached"]),
      module_reports: reports,
      theorem_timings_available: Enum.any?(reports, &(&1["theorems"] != []))
    }
  end

  defp workloads(opts, env, build, artifacts) do
    Enum.flat_map(opts[:workloads], fn name ->
      clear_cache(build)

      for repetition <- 0..opts[:repetitions] do
        phase = phase(repetition)

        expression =
          "ReductionBounds.Benchmark.Workloads.run(System.fetch_env!(\"REDUCTION_BOUNDS_BENCH_WORKLOAD\"))"

        run(
          name,
          phase,
          ["run", "--no-compile", "-e", expression],
          [{"REDUCTION_BOUNDS_BENCH_WORKLOAD", name} | env],
          artifacts,
          opts[:output]
        )
      end
    end)
  end

  defp suite(opts, env, build, artifacts) do
    if opts[:suite] do
      clear_cache(build)

      [
        run(
          "suite",
          "cold",
          ["test", "--seed", to_string(opts[:seed]), "--max-cases", to_string(opts[:max_cases])],
          env,
          artifacts,
          opts[:output]
        )
      ]
    else
      []
    end
  end

  defp run(name, phase, args, env, artifacts, output) do
    Mix.shell().info("Measuring #{name}: #{phase}")
    basename = Path.join(artifacts, "#{name}_#{phase}")
    events_path = basename <> ".jsonl"
    File.write!(events_path, "")

    command =
      Command.run(
        "mix",
        args,
        [{"REDUCTION_BOUNDS_BENCH_EVENTS", events_path} | env],
        basename <> ".log"
      )

    events =
      events_path |> File.read!() |> String.split("\n", trim: true) |> Enum.map(&JSON.decode!/1)

    result =
      Map.merge(command, %{
        workload: name,
        phase: phase,
        events: events_path,
        verification: summarize(events)
      })

    checkpoint = output |> File.read!() |> JSON.decode!()
    write_report(output, Map.update!(checkpoint, "runs", &(&1 ++ [result])))
    result
  end

  # Only this invocation's fresh build is touched; never clear the caller's cache.
  defp clear_cache(build), do: File.rm_rf!(Path.join(build, "lynx"))

  defp phase(0), do: "cold"
  defp phase(repetition), do: "warm_#{repetition}"

  defp write_report(path, report) do
    File.write!(path <> ".tmp", [JSON.encode!(report), "\n"])
    File.rename!(path <> ".tmp", path)
  end

  defp metadata(opts, workspace) do
    %{
      captured_at: DateTime.utc_now() |> DateTime.to_iso8601(),
      source_revision: command_output("git", ["rev-parse", "HEAD"]),
      source_status: command_output("git", ["status", "--porcelain"]),
      tracked_diff_sha256: digest(command_output("git", ["diff", "HEAD"])),
      lockfile_sha256: File.read!("mix.lock") |> digest(),
      dependencies: dependency_revisions(),
      elixir: System.version(),
      otp: :erlang.system_info(:otp_release) |> List.to_string(),
      otp_version: otp_version(),
      erts: :erlang.system_info(:version) |> List.to_string(),
      lean: command_output("lean", ["--version"]),
      lake: command_output("lake", ["--version"]),
      lean_toolchain: File.read!("lean-toolchain") |> String.trim(),
      system: command_output("uname", ["-a"]),
      processors: :erlang.system_info(:logical_processors),
      processors_available: :erlang.system_info(:logical_processors_available),
      schedulers_online: System.schedulers_online(),
      memory_total_bytes: physical_memory(),
      container_memory_max: read_resource("/sys/fs/cgroup/memory.max"),
      container_cpu_max: read_resource("/sys/fs/cgroup/cpu.max"),
      environment:
        Map.new(
          ~w(ERL_FLAGS ELIXIR_ERL_OPTIONS LEAN_NUM_THREADS ELAN_TOOLCHAIN REDUCTION_BOUNDS_PROOF_CACHE REDUCTION_BOUNDS_PROOF_MODE),
          &{&1, System.get_env(&1)}
        ),
      suite_max_cases: opts[:max_cases],
      target_max_concurrency: 2,
      target_timeout_ms: 60_000,
      suite_seed: opts[:seed],
      suite_runs: if(opts[:suite], do: 1, else: 0),
      warm_repetitions: opts[:repetitions],
      workloads: opts[:workloads],
      workspace: workspace,
      workspace_retained: opts[:keep_workspace],
      lean_build_already_present:
        File.exists?(
          Path.join(ReductionBounds.Verification.project_dir(), ".lake/build/bin/Lynx-Runner")
        ),
      verification_cache_policy: %{
        integer_mode: System.get_env("REDUCTION_BOUNDS_PROOF_MODE", "named"),
        integer_cache: System.get_env("REDUCTION_BOUNDS_PROOF_CACHE", "on"),
        other_families: "uncached",
        untracked_external_imports: "uncached with dependents"
      },
      timing_scope:
        "preparation is an isolated Mix build; existing dependency Lean build artifacts may be reused",
      overhead_scope:
        "runner non-module wall time includes Lake/process startup, shared runtime loading, protocol and teardown; not individually observable through the pinned API",
      memory_scope:
        "100 ms samples of summed process-tree RSS; shared pages may be counted more than once; null if unavailable",
      aggregation_scope:
        "request duration sums may overlap during the suite; use command wall_ms for throughput"
    }
  end

  defp dependency_revisions() do
    Map.new(Lock.read(), fn
      {name, {:git, url, revision, _opts}} -> {name, %{source: url, revision: revision}}
      {name, {:hex, _, version, _, _, _, _, _}} -> {name, %{version: version}}
    end)
  end

  defp otp_version() do
    root = :code.root_dir() |> List.to_string()
    release = :erlang.system_info(:otp_release) |> List.to_string()
    read_resource(Path.join([root, "releases", release, "OTP_VERSION"]))
  end

  defp read_resource(path) do
    case File.read(path) do
      {:ok, contents} -> String.trim(contents)
      _ -> nil
    end
  end

  defp physical_memory() do
    case File.read("/proc/meminfo") do
      {:ok, contents} ->
        case Regex.run(~r/^MemTotal:\s+(\d+) kB/m, contents) do
          [_, kb] -> String.to_integer(kb) * 1024
          _ -> nil
        end

      _ ->
        nil
    end
  end

  defp command_output(executable, args) do
    case System.cmd(executable, args, stderr_to_stdout: true) do
      {text, 0} -> String.trim(text)
      _ -> nil
    end
  rescue
    _error -> nil
  end

  defp digest(nil), do: nil
  defp digest(value), do: :crypto.hash(:sha256, value) |> Base.encode16(case: :lower)
end
