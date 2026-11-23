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

  test "rejects invalid benchmark options before preparing any build" do
    for args <- [
          ["--repetitions", "0"],
          ["--max-cases", "0"],
          ["--workloads", "unknown"],
          ["--trace"]
        ] do
      assert_raise Mix.Error, fn -> Mix.Tasks.ReductionBounds.Bench.run(args) end
    end
  end
end
