defmodule Mix.Tasks.ReductionBounds.Bench do
  @shortdoc "Measures verification workflows and the full suite in an isolated build"
  @moduledoc """
  Records a baseline without changing verification semantics or clearing normal caches.

      mix reduction_bounds.bench --output _build/baseline.json
      mix reduction_bounds.bench --no-suite --workloads integer_cost,list --repetitions 1

  Options: `--output PATH`, `--workloads NAMES` (comma-separated),
  `--repetitions N` (warm workload runs, default 3), `--[no-]suite` (default true),
  `--max-cases N`, `--seed N`, and `--keep-workspace`.

  Logs and per-request events are saved beside the JSON report. Each workload has
  one cold-cache run followed by warm attempts in fresh VMs. The full suite
  runs once when enabled. The current backend
  disables persistent verification caching, so warm attempts still recheck proofs.
  See `docs/benchmarking.md` for timing and memory interpretation.
  """

  use Mix.Task

  alias ReductionBounds.Benchmark
  alias ReductionBounds.Benchmark.Workloads

  @impl true
  def run(args) do
    {opts, rest, invalid} =
      OptionParser.parse(args,
        strict: [
          output: :string,
          workloads: :string,
          repetitions: :integer,
          suite: :boolean,
          max_cases: :integer,
          seed: :integer,
          keep_workspace: :boolean
        ]
      )

    if rest != [] or invalid != [],
      do: Mix.raise("invalid benchmark arguments: #{inspect(rest ++ invalid)}")

    defaults = [
      output: Path.join(Mix.Project.build_path(), "reduction_bounds_bench/report.json"),
      repetitions: 3,
      suite: true,
      max_cases: System.schedulers_online() * 2,
      seed: 0,
      keep_workspace: false
    ]

    opts = Keyword.merge(defaults, opts)

    names =
      if opts[:workloads],
        do: String.split(opts[:workloads], ",", trim: true),
        else: Workloads.names()

    unless names != [] and Enum.all?(names, &(&1 in Workloads.names())),
      do: Mix.raise("workloads must be selected from #{Enum.join(Workloads.names(), ",")}")

    unless opts[:repetitions] >= 1 and opts[:max_cases] >= 1 and opts[:seed] >= 0,
      do: Mix.raise("repetitions and max-cases must be positive; seed must be nonnegative")

    Benchmark.run(Keyword.put(opts, :workloads, Enum.uniq(names)))
  end
end
