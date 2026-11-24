# cspell:words uncacheable
defmodule ReductionBounds.Benchmark.Opportunities do
  @moduledoc false

  @spec summarize([map()]) :: map()
  def summarize(events) do
    completed = Enum.filter(events, &(&1["event"] == "completed"))
    accepted = Enum.filter(completed, &accepted?/1)
    shared = for event <- accepted, report <- event["reports"], shared?(report), do: report

    %{
      request_groups:
        completed
        |> Enum.group_by(&group/1)
        |> Map.new(fn {name, requests} -> {name, timing(requests)} end),
      accepted_shared_modules: %{
        cache_hits: Enum.count(shared, & &1["cached"]),
        cacheable_misses: Enum.count(shared, &cacheable_miss?/1),
        uncacheable_misses: Enum.count(shared, &(not &1["cached"] and &1["cacheable"] == false)),
        unknown_policy_misses:
          Enum.count(shared, &(not &1["cached"] and is_nil(&1["cacheable"]))),
        cacheable_miss_module_ms_sum:
          sum_available(for report <- shared, cacheable_miss?(report), do: report["time_ms"])
      },
      interpretation: %{
        runner_residual:
          "call time minus paired module reports; excludes preparation/admission waiting, not isolated startup",
        shared_misses:
          "cacheable misses in accepted requests only; module time includes imports/rendering/auditing/publication",
        cold_dag:
          "no dependency critical path, ready-frontier timing or scheduler benefit is measured",
        throughput: "concurrent request sums overlap; use ordinary command wall time",
        decision:
          "runner reuse and cold DAG scheduling remain conditional; no backend or default is selected"
      }
    }
  end

  defp accepted?(event) do
    reports = event["reports"]
    reports != [] and Enum.all?(reports, &(&1["status"] == "ok"))
  end

  defp group(%{"reports" => []}), do: "empty_probe"

  defp group(event) do
    reports = event["reports"]

    cond do
      not accepted?(event) -> "unsuccessful"
      Enum.all?(reports, & &1["cached"]) -> "fully_cached"
      Enum.any?(reports, &(shared?(&1) and cacheable_miss?(&1))) -> "shared_cacheable_miss"
      Enum.any?(reports, &(&1["cacheable"] == false)) -> "uncacheable_or_bypassed"
      Enum.any?(reports, &is_nil(&1["cacheable"])) -> "policy_unknown"
      true -> "target_or_other_miss"
    end
  end

  defp shared?(report), do: String.starts_with?(report["module"], "ReductionBounds.Proofs.")
  defp cacheable_miss?(report), do: not report["cached"] and report["cacheable"] == true

  defp timing(requests) do
    calls = Enum.map(requests, &call_time/1)
    pairs = Enum.map(requests, &pair/1)
    valid = for {:ok, call, modules} <- pairs, do: {call, modules}

    %{
      requests: length(requests),
      runner_calls_with_time: Enum.count(calls, &is_number/1),
      runner_call_wall_ms_sum: sum_available(calls),
      paired_requests: length(valid),
      paired_module_wall_ms_sum: sum_available(Enum.map(valid, &elem(&1, 1))),
      paired_runner_non_module_wall_ms_sum:
        sum_available(Enum.map(valid, fn {call, modules} -> call - modules end)),
      missing_timing_requests: Enum.count(pairs, &(&1 == :missing)),
      inconsistent_timing_requests: Enum.count(pairs, &(&1 == :inconsistent))
    }
  end

  defp call_time(event) do
    case event["job"] do
      %{"runner_call_wall_ms" => ms} when is_number(ms) and ms >= 0 -> ms
      _ -> nil
    end
  end

  defp pair(event) do
    call = call_time(event)
    times = Enum.map(event["reports"], & &1["time_ms"])

    if is_number(call) and Enum.all?(times, &(is_number(&1) and &1 >= 0)) do
      modules = Enum.sum(times)
      if call >= modules, do: {:ok, call, modules}, else: :inconsistent
    else
      :missing
    end
  end

  defp sum_available(values) do
    case Enum.filter(values, &is_number/1) do
      [] -> nil
      times -> Enum.sum(times)
    end
  end
end
