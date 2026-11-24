defmodule ReductionBounds.CalibrationTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.Benchmark.Calibration

  test "plans sequential fresh trials with rotated job order and explicit child settings" do
    plan =
      Calibration.plan(
        [
          jobs: [2, 4, 1],
          lean_threads: 2,
          seed: 7,
          max_cases: 24,
          suite_repetitions: 2,
          trials: 2,
          test_files: "test/reduction_bounds/benchmark_test.exs"
        ],
        "/tmp/calibration"
      )

    assert Enum.map(plan, & &1.jobs) == [2, 4, 1, 4, 1, 2]
    assert length(Enum.uniq_by(plan, & &1.report)) == 6
    assert length(JSON.decode!(JSON.encode!(plan))) == 6

    assert Enum.all?(plan, fn entry ->
             env = Map.new(entry.env)

             env["REDUCTION_BOUNDS_LEAN_JOBS"] == to_string(entry.jobs) and
               env["LEAN_NUM_THREADS"] == "2" and env["REDUCTION_BOUNDS_PROOF_MODE"] == "named" and
               env["REDUCTION_BOUNDS_PROOF_CACHE"] == "on"
           end)

    assert hd(plan).args == [
             "reduction_bounds.bench",
             "--suite-only",
             "--seed",
             "7",
             "--max-cases",
             "24",
             "--suite-repetitions",
             "2",
             "--output",
             "/tmp/calibration/trial-1-jobs-2.json",
             "--test-files",
             "test/reduction_bounds/benchmark_test.exs"
           ]
  end

  test "keeps cold and warm statistics separate and retains intentional negative request counts" do
    comparison =
      Calibration.summarize([result(2, 100, 40), result(2, 120, 50), result(4, 80, 30)])

    assert comparison.comparable
    assert comparison.scope == "full"
    [cold, warm | _rest] = comparison.measurements
    assert cold.command_wall_ms_median == 110
    assert cold.command_wall_ms_min == 100
    assert cold.command_wall_ms_max == 120
    assert warm.command_wall_ms_median == 45
    assert warm.samples == 2
    assert warm.failed_requests == [2, 2]
    assert warm.incomplete_requests == [4, 4]
    assert warm.sampled_peak_tree_rss_bytes_max == nil
    assert warm.sampled_tree_cpu_percent_median == nil
    assert Calibration.markdown(comparison) =~ "No default is selected automatically"
  end

  test "rejects a failed suite, excessive admission, missing phases, and missing reports" do
    base = result(2, 100, 40)

    bad = [
      %{base | exit_status: 1},
      update_in(base, [:benchmark, "runs", Access.at(0), "exit_status"], fn _ -> 1 end),
      update_in(
        base,
        [:benchmark, "runs", Access.at(0), "verification", "peak_active_jobs"],
        fn _ -> 3 end
      ),
      update_in(base, [:benchmark, "runs", Access.at(0), "verification", "suite"], fn _ -> nil end),
      update_in(base, [:benchmark, "runs"], &tl/1),
      update_in(base, [:benchmark, "runs", Access.at(1), "phase"], fn _ -> "cold" end),
      %{base | benchmark: nil}
    ]

    for changed <- bad do
      comparison = Calibration.summarize([base, changed])
      refute comparison.comparable
      assert comparison.issues != []
    end
  end

  test "rejects source, toolchain, cache, thread, suite selection and test-count mismatches" do
    base = result(2, 100, 40)

    metadata_changes = [
      {["source_revision"], "other"},
      {["source_status"], " M mix.exs"},
      {["lean"], "other Lean"},
      {["lockfile_sha256"], "different"},
      {["suite_seed"], 1},
      {["suite_max_cases"], 4},
      {["suite_files"], ["selected_test.exs"]},
      {["environment", "LEAN_NUM_THREADS"], "4"},
      {["environment", "REDUCTION_BOUNDS_PROOF_CACHE"], "off"},
      {["global_lean_jobs"], 4}
    ]

    for {path, value} <- metadata_changes do
      changed = put_in(base, [:benchmark, "metadata"] ++ path, value)
      refute Calibration.summarize([base, changed]).comparable
    end

    changed =
      put_in(base, [:benchmark, "runs", Access.at(1), "verification", "tests", "count"], 9)

    refute Calibration.summarize([base, changed]).comparable
    changed = put_in(base, [:source_after, "source_revision"], "other")
    refute Calibration.summarize([base, changed]).comparable
  end

  test "labels selected-suite results and rejects empty comparisons" do
    selected =
      put_in(result(2, 100, 40), [:benchmark, "metadata", "suite_files"], ["one_test.exs"])

    assert Calibration.summarize([selected]).scope == "selected"
    refute Calibration.summarize([]).comparable
  end

  test "rejects invalid CLI options before starting any benchmark" do
    for args <- [
          ["--jobs", ""],
          ["--jobs", "2,0"],
          ["--jobs", "2,2"],
          ["--jobs", "2"],
          ["--jobs", "2,,4"],
          ["--lean-threads", "0"],
          ["--max-cases", "0"],
          ["--seed", "-1"],
          ["--trials", "0"],
          ["--suite-repetitions", "0"],
          ["--test-files", ""],
          ["--test-files", "mix.exs"],
          ["--trace"]
        ] do
      assert_raise Mix.Error, fn -> Mix.Tasks.ReductionBounds.Calibrate.run(args) end
    end
  end

  defp result(jobs, cold, warm) do
    metadata = %{
      "source_revision" => "commit",
      "source_status" => "",
      "global_lean_jobs" => jobs,
      "suite_runs" => 2,
      "suite_files" => [],
      "suite_seed" => 0,
      "suite_max_cases" => 24,
      "environment" => %{
        "REDUCTION_BOUNDS_LEAN_JOBS" => to_string(jobs),
        "LEAN_NUM_THREADS" => "2",
        "REDUCTION_BOUNDS_PROOF_MODE" => "named",
        "REDUCTION_BOUNDS_PROOF_CACHE" => "on"
      }
    }

    %{
      jobs: jobs,
      exit_status: 0,
      source_after: Map.take(metadata, ~w(source_revision source_status)),
      benchmark: %{
        "status" => "completed",
        "metadata" => metadata,
        "runs" => [run(jobs, "cold", cold), run(jobs, "warm_1", warm)]
      }
    }
  end

  defp run(jobs, phase, wall) do
    %{
      "workload" => "suite",
      "phase" => phase,
      "wall_ms" => wall,
      "exit_status" => 0,
      "verification" => %{
        "suite" => %{},
        "tests" => %{"count" => 10},
        "peak_active_jobs" => jobs,
        "job_queue_ms_sum" => 5,
        "coordination_wall_ms_sum" => 3,
        "runner_calls_started" => 8,
        "cached_modules" => 4,
        "failed_requests" => 2,
        "incomplete_requests" => 4
      }
    }
  end
end
