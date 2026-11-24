defmodule ReductionBounds.OptimizationEvidenceTest do
  use ExUnit.Case, async: true

  import ExUnit.CaptureIO
  alias ReductionBounds.Benchmark
  alias ReductionBounds.Benchmark.Opportunities
  alias Mix.Tasks.ReductionBounds.Assess

  test "actual call residual excludes waiting and rejected requests stay separate" do
    warm =
      completed(
        [
          report("ReductionBounds.Proofs.Size", true, true, 3),
          report("Erlang.postlude", true, true, 2)
        ],
        20
      )

    failed =
      completed(
        [%{report("ReductionBounds.Proofs.Size", false, true, 7) | "status" => "error"}],
        10
      )

    summary = Benchmark.summarize([warm, failed]).optimization_evidence
    stats = summary.request_groups["fully_cached"]
    assert stats.runner_call_wall_ms_sum == 20
    assert stats.paired_module_wall_ms_sum == 5
    assert stats.paired_runner_non_module_wall_ms_sum == 15
    assert summary.request_groups["unsuccessful"].requests == 1
    assert summary.accepted_shared_modules.cache_hits == 1
    assert summary.accepted_shared_modules.cacheable_misses == 0
  end

  test "uncached reports distinguish cacheable misses, bypass and unknown legacy policy" do
    shared = "ReductionBounds.Proofs.Size"

    events = [
      completed([report(shared, false, true, 8)], 10),
      completed([report(shared, false, false, 8)], 10),
      completed([Map.delete(report(shared, false, true, 8), "cacheable")], 10),
      completed([report("Erlang.postlude", false, true, 2)], 10)
    ]

    summary = Opportunities.summarize(events)

    assert Map.keys(summary.request_groups) |> Enum.sort() ==
             Enum.sort([
               "shared_cacheable_miss",
               "uncacheable_or_bypassed",
               "policy_unknown",
               "target_or_other_miss"
             ])

    assert summary.accepted_shared_modules.cacheable_misses == 1
    assert summary.accepted_shared_modules.uncacheable_misses == 1
    assert summary.accepted_shared_modules.unknown_policy_misses == 1
    assert summary.accepted_shared_modules.cacheable_miss_module_ms_sum == 8
  end

  test "missing and inconsistent timing cannot become estimated startup or zero overhead" do
    reports = [report("Erlang.postlude", true, true, 5)]
    missing = Map.delete(completed(reports, 10), "job")
    inconsistent = completed(reports, 2)
    summary = Opportunities.summarize([missing, inconsistent, completed([], 0)])
    stats = summary.request_groups["fully_cached"]
    assert stats.runner_calls_with_time == 1
    assert stats.runner_call_wall_ms_sum == 2
    assert stats.paired_requests == 0
    assert stats.paired_runner_non_module_wall_ms_sum == nil
    assert stats.missing_timing_requests == 1
    assert stats.inconsistent_timing_requests == 1
    assert summary.request_groups["empty_probe"].paired_runner_non_module_wall_ms_sum == 0
  end

  @tag :tmp_dir
  test "assesses relocated artifacts without modifying the benchmark or running Lean", %{
    tmp_dir: dir
  } do
    input = Path.join(dir, "source.json")
    output = Path.join(dir, "review.json")
    artifacts = Path.join(dir, "source_artifacts")
    File.mkdir!(artifacts)

    File.write!(
      Path.join(artifacts, "run.jsonl"),
      JSON.encode!(completed([report("Erlang.postlude", true, true, 5)], 20)) <> "\n"
    )

    source =
      JSON.encode!(%{
        status: "completed",
        metadata: %{source_revision: "measured"},
        runs: [
          %{
            events: "/old/workspace/run.jsonl",
            workload: "suite",
            phase: "cold",
            wall_ms: 100,
            exit_status: 0
          }
        ]
      })

    File.write!(input, source)
    capture_io(fn -> Assess.run([input, "--output", output]) end)
    assessment = output |> File.read!() |> JSON.decode!()
    assert assessment["status"] == "complete"
    assert assessment["benchmark_status"] == "completed"

    assert assessment["runs"]
           |> hd()
           |> get_in([
             "evidence",
             "request_groups",
             "fully_cached",
             "paired_runner_non_module_wall_ms_sum"
           ]) == 15

    assert File.read!(input) == source
    assert File.read!(Path.rootname(output) <> ".md") =~ "not isolated startup"
  end

  @tag :tmp_dir
  test "missing adjacent events stay unavailable even if a saved absolute path exists", %{
    tmp_dir: dir
  } do
    foreign = Path.join(dir, "foreign.jsonl")
    File.write!(foreign, "invalid JSON that must not be read\n")
    input = Path.join(dir, "source.json")
    output = Path.join(dir, "review.json")
    File.write!(input, JSON.encode!(%{runs: [%{events: foreign}]}))

    capture_io(fn ->
      assert_raise Mix.Error, ~r/events are missing/, fn ->
        Assess.run([input, "--output", output])
      end
    end)

    result = output |> File.read!() |> JSON.decode!()
    assert result["status"] == "incomplete"
    assert hd(result["runs"])["events_status"] == "missing"
  end

  @tag :tmp_dir
  test "assessment rejects invalid arguments and refuses to overwrite existing inputs or outputs",
       %{tmp_dir: dir} do
    assert_raise Mix.Error, fn -> Assess.run(["--trace"]) end
    input = Path.join(dir, "source.json")
    File.write!(input, JSON.encode!(%{runs: []}))
    assert_raise Mix.Error, fn -> Assess.run([input, "--output", input]) end
    output = Path.join(dir, "existing.json")
    File.write!(output, "preserve")
    assert_raise Mix.Error, fn -> Assess.run([input, "--output", output]) end
    assert File.read!(output) == "preserve"
  end

  defp report(module, cached, cacheable, time) do
    %{
      "module" => module,
      "status" => "ok",
      "cached" => cached,
      "cacheable" => cacheable,
      "time_ms" => time,
      "theorems" => []
    }
  end

  defp completed(reports, call) do
    %{
      "event" => "completed",
      "reports" => reports,
      "assembly_ms" => 1,
      "runner_wall_ms" => 10_000,
      "runner_non_module_wall_ms" => 9_995,
      "job" => %{"runner_call_wall_ms" => call}
    }
  end
end
