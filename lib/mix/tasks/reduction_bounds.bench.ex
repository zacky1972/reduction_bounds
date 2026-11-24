defmodule Mix.Tasks.ReductionBounds.Bench do
  @shortdoc "Measures verification workflows and the full suite in an isolated build"
  @moduledoc """
  Records a baseline without changing verification semantics or clearing normal caches.

      mix reduction_bounds.bench --output _build/baseline.json
      mix reduction_bounds.bench --no-suite --workloads integer_cost,list --repetitions 1

  Options: `--output PATH`, `--workloads NAMES` (comma-separated),
  `--repetitions N` (warm workload runs, default 3), `--[no-]suite` (default true),
  `--max-cases N`, `--seed N`, and `--keep-workspace`.
  Use `--suite-only` to profile just the ordinary suite; `--suite-repetitions N`
  adds N warm suite runs after the cold run. With `--suite-only`, use
  `--test-files PATHS` (comma-separated) to compare a selected test cohort. Test timings are recorded without
  enabling trace mode. REDUCTION_BOUNDS_LEAN_JOBS sets the per-VM job limit (default 2).

  Logs and per-request events are saved beside the JSON report. Each workload has
  one cold-cache run followed by warm attempts in fresh VMs. The full suite
  runs once when enabled. Packaged proof families reuse checked shared modules
  and target artifacts; overlapping cold preparation is coalesced in each VM. Set
  REDUCTION_BOUNDS_PROOF_CACHE=off to recheck all modules, or
  REDUCTION_BOUNDS_PROOF_MODE=embedded to compare the original embedded-source path.
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
          suite_only: :boolean,
          test_files: :string,
          suite_repetitions: :integer,
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
      suite_only: false,
      suite_repetitions: 0,
      max_cases: System.schedulers_online() * 2,
      seed: 0,
      keep_workspace: false
    ]

    opts = Keyword.merge(defaults, opts)

    validate_suite!(opts)
    validate_numbers!(opts)
    names = if opts[:suite_only], do: [], else: selected_workloads(opts)

    unless (names != [] or opts[:suite_only]) and Enum.all?(names, &(&1 in Workloads.names())),
      do: Mix.raise("invalid workload selection")

    opts = Keyword.put(opts, :suite_files, selected_test_files(opts))
    Benchmark.run(Keyword.put(opts, :workloads, Enum.uniq(names)))
  end

  defp validate_suite!(opts) do
    if opts[:test_files] && not opts[:suite_only],
      do: Mix.raise("test-files requires suite-only")

    if opts[:suite_only] and (not opts[:suite] or opts[:workloads]),
      do: Mix.raise("suite-only requires suite and cannot select workloads")

    if opts[:workloads] == "", do: Mix.raise("workloads cannot be empty")
  end

  defp validate_numbers!(opts) do
    unless opts[:repetitions] >= 1 and opts[:max_cases] >= 1 and opts[:seed] >= 0 and
             opts[:suite_repetitions] >= 0,
           do:
             Mix.raise(
               "repetitions and max-cases must be positive; seed and suite-repetitions must be nonnegative"
             )
  end

  defp selected_test_files(opts) do
    files = String.split(opts[:test_files] || "", ",", trim: true)
    if opts[:test_files] && files == [], do: Mix.raise("test-files cannot be empty")
    Enum.each(files, &validate_test_file!/1)
    files
  end

  defp validate_test_file!(file) do
    unless String.starts_with?(Path.expand(file), Path.expand("test") <> "/") and
             String.ends_with?(file, "_test.exs") and File.regular?(file),
           do: Mix.raise("test-files must select existing test files inside test/")
  end

  defp selected_workloads(opts) do
    if opts[:workloads],
      do: String.split(opts[:workloads], ",", trim: true),
      else: Workloads.names()
  end
end
