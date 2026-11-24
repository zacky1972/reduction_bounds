# cspell:words rootname
defmodule Mix.Tasks.ReductionBounds.Assess do
  @shortdoc "Reviews runner timing and cache evidence from an existing benchmark"
  @moduledoc """
  Reprocesses benchmark events without running Lean or changing configuration.

      mix reduction_bounds.assess _build/suite.json --output _build/review.json

  Reads each run's JSONL events from the sibling `<report>_artifacts` directory.
  This also works for relocated baseline reports with their adjacent artifacts.
  Missing events are reported explicitly; saved absolute paths are not followed.
  Legacy events without actual call timing or cache-policy fields remain unknown.
  The JSON and adjacent Markdown summary support a conditional optimization review;
  neither reusable runners nor cold dependency scheduling are enabled or recommended
  automatically. See `docs/runner_optimization_review.md` for the decision criteria.
  """

  use Mix.Task

  alias ReductionBounds.Benchmark.Opportunities

  @impl true
  def run(args) do
    {input, output} = arguments!(args)
    markdown = Path.rootname(output) <> ".md"
    ensure_new_output!(input, output, markdown)
    benchmark = read_benchmark!(input)
    artifacts = Path.rootname(input) <> "_artifacts"

    runs = Enum.map(benchmark["runs"], &assess(&1, artifacts))

    status =
      if runs != [] and Enum.all?(runs, &(&1.events_status == :available)),
        do: :complete,
        else: :incomplete

    report = %{
      benchmark_status: benchmark["status"],
      schema_version: 1,
      status: status,
      input: input,
      metadata: benchmark["metadata"],
      runs: runs,
      decision:
        "deferred: review controlled throughput, attribution, supported APIs and lifecycle checks before implementing either optimization"
    }

    File.mkdir_p!(Path.dirname(output))
    File.write!(output, [JSON.encode!(report), "\n"])
    File.write!(markdown, markdown(report))
    Mix.shell().info("Optimization evidence: #{output}")
    if status == :incomplete, do: Mix.raise("assessment events are missing; see #{output}")
  end

  defp arguments!(args) do
    {opts, paths, invalid} = OptionParser.parse(args, strict: [output: :string])

    unless length(paths) == 1 and invalid == [] and opts[:output],
      do: Mix.raise("usage: mix reduction_bounds.assess REPORT.json --output REVIEW.json")

    {Path.expand(hd(paths)), Path.expand(opts[:output])}
  end

  defp ensure_new_output!(input, output, markdown) do
    if input in [output, markdown] or File.exists?(output) or File.exists?(markdown),
      do: Mix.raise("choose a new assessment output path")
  end

  defp read_benchmark!(input) do
    benchmark = input |> File.read!() |> JSON.decode!()

    unless is_map(benchmark) and is_list(benchmark["runs"]),
      do: Mix.raise("input must be a benchmark report with runs")

    benchmark
  end

  defp assess(run, artifacts) do
    result = %{
      workload: run["workload"],
      phase: run["phase"],
      command_wall_ms: run["wall_ms"],
      exit_status: run["exit_status"]
    }

    path = if is_binary(run["events"]), do: Path.join(artifacts, Path.basename(run["events"]))

    if path && File.regular?(path) do
      events = path |> File.read!() |> String.split("\n", trim: true) |> Enum.map(&JSON.decode!/1)
      Map.merge(result, %{events_status: :available, evidence: Opportunities.summarize(events)})
    else
      Map.put(result, :events_status, :missing)
    end
  end

  defp markdown(report) do
    runs =
      Enum.map(report.runs, fn run ->
        rows =
          for {group, stats} <- get_in(run, [:evidence, :request_groups]) || %{} do
            "| #{group} | #{stats.requests} | #{stats.paired_requests} | #{inspect(stats.runner_call_wall_ms_sum)} | #{inspect(stats.paired_runner_non_module_wall_ms_sum)} |"
          end

        Enum.join(
          [
            "## #{run.workload} / #{run.phase}",
            "",
            "Events: #{run.events_status}. Command wall: #{inspect(run.command_wall_ms)} ms. Exit: #{inspect(run.exit_status)}.",
            "",
            "| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |",
            "| --- | ---: | ---: | ---: | ---: |",
            Enum.join(Enum.sort(rows), "\n"),
            ""
          ],
          "\n"
        )
      end)

    Enum.join(
      [
        "# Conditional runner optimization review",
        "",
        "Evidence: #{report.status}. Benchmark status: #{inspect(report.benchmark_status)}.",
        report.decision,
        "",
        Enum.join(runs, "\n"),
        "Residuals exclude preparation/admission waits and are not isolated startup measurements. Sums overlap and are not suite-time partitions. Missing policy is unknown; an uncached report alone does not prove a cacheable cold miss. A complete event review does not mean a passing benchmark or justify either backend change.",
        ""
      ],
      "\n"
    )
  end
end
