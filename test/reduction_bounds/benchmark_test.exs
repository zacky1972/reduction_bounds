defmodule ReductionBounds.BenchmarkTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.Benchmark
  alias ReductionBounds.Benchmark.Command

  test "summaries distinguish missing theorem timings, cached modules, and interrupted requests" do
    events = [
      %{"event" => "started"},
      %{
        "event" => "completed",
        "assembly_ms" => 1.5,
        "runner_wall_ms" => 12.0,
        "runner_non_module_wall_ms" => 10.0,
        "reports" => [
          %{"module" => "common", "cached" => true, "time_ms" => 0, "theorems" => []},
          %{"module" => "target", "cached" => false, "time_ms" => 2, "theorems" => []}
        ]
      },
      %{"event" => "started"},
      %{"event" => "failed"},
      %{"event" => "started"}
    ]

    result = Benchmark.summarize(events)
    assert result.started_requests == 3
    assert result.completed_requests == 1
    assert result.failed_requests == 1
    assert result.incomplete_requests == 1
    assert result.cached_modules == 1
    assert result.assembly_ms == 1.5
    refute result.theorem_timings_available
  end

  @tag :tmp_dir
  test "command measurements preserve output and nonzero exit status", %{tmp_dir: dir} do
    log = Path.join(dir, "command.log")
    result = Command.run("sh", ["-c", "printf 'benchmark output'; exit 7"], [], log)
    assert result.exit_status == 7
    assert result.wall_ms >= 0
    assert File.read!(log) == "benchmark output"
    assert result.memory_sampling_interval_ms == 100
  end

  test "parses Linux and macOS process CPU clocks" do
    assert Command.cpu_ms("00:01:02") == 62_000
    assert Command.cpu_ms("1-02:03:04") == 93_784_000
    assert Command.cpu_ms("1:02.35") == 62_350
  end

  test "summarizes test costs and actual job admission separately" do
    events = [
      %{"event" => "runner_started", "job" => %{"queue_ms" => 12.0, "active_at_start" => 2}},
      %{"event" => "phase", "stage" => "source_generation", "wall_ms" => 3.0},
      %{
        "event" => "test_finished",
        "module" => "ProofTest",
        "test" => "first",
        "async" => false,
        "wall_ms" => 40.0
      },
      %{
        "event" => "test_finished",
        "module" => "ProofTest",
        "test" => "second",
        "async" => false,
        "wall_ms" => 20.0
      }
    ]

    summary = Benchmark.summarize(events)
    assert summary.runner_calls_started == 1
    assert summary.job_queue_ms_sum == 12.0
    assert summary.peak_active_jobs == 2
    assert summary.phase_wall_ms_sums == %{"source_generation" => 3.0}
    assert [%{module: "ProofTest", test_wall_ms_sum: 60.0, async: false}] = summary.tests.modules
    assert hd(summary.tests.slowest)["test"] == "first"
  end

  test "rejects invalid benchmark options before preparing any build" do
    for args <- [
          ["--repetitions", "0"],
          ["--max-cases", "0"],
          ["--workloads", "unknown"],
          ["--workloads", ",,"],
          ["--trace"],
          ["--suite-only", "--no-suite"],
          ["--suite-repetitions", "-1"]
        ] do
      assert_raise Mix.Error, fn -> Mix.Tasks.ReductionBounds.Bench.run(args) end
    end
  end
end
