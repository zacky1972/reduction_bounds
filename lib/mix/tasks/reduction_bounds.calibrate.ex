defmodule Mix.Tasks.ReductionBounds.Calibrate do
  @shortdoc "Compares Lean job budgets sequentially with controlled suite settings"
  @moduledoc """
  Runs the ordinary suite with isolated cold/warm verification caches for each job budget.

      mix reduction_bounds.calibrate --jobs 2,4,1 --lean-threads 2 \\
        --seed 0 --max-cases 24 --suite-repetitions 1 --trials 1 \\
        --output _build/job-calibration.json

  `--jobs` defaults to `2,4,1`; `--lean-threads` to 2; `--seed` to 0;
  `--max-cases` to 24; `--suite-repetitions` to 1 warm run; and `--trials` to 1.
  Trials use fresh isolated builds/caches, rotating the job order between trials.
  `--test-files PATHS` optionally selects comma-separated test files, as in the
  benchmark task. Selected-suite results do not establish a full-suite default.

  Jobs are sequential, never simultaneous. Child VMs receive explicit job/thread
  settings and named proofs with caching enabled; the parent environment is not changed.
  Source/toolchain/settings mismatches or failed suites invalidate the comparison.
  Use a clean committed checkout and a new output path. Reports include raw logs,
  per-request events, a JSON comparison and a Markdown table. No default is changed.
  """

  use Mix.Task

  alias ReductionBounds.Benchmark.Calibration

  @impl true
  def run(args) do
    {opts, rest, invalid} =
      OptionParser.parse(args,
        strict: [
          jobs: :string,
          lean_threads: :integer,
          seed: :integer,
          max_cases: :integer,
          suite_repetitions: :integer,
          trials: :integer,
          output: :string,
          test_files: :string
        ]
      )

    if rest != [] or invalid != [], do: Mix.raise("invalid calibration arguments")

    opts =
      Keyword.merge(
        [
          jobs: "2,4,1",
          lean_threads: 2,
          seed: 0,
          max_cases: 24,
          suite_repetitions: 1,
          trials: 1,
          output: "_build/job-calibration.json"
        ],
        opts
      )

    opts = Keyword.put(opts, :jobs, jobs!(opts[:jobs]))
    validate!(opts)
    Calibration.run(opts)
  end

  defp jobs!(text) do
    jobs = Enum.map(String.split(text, ","), &Integer.parse/1)

    unless Enum.all?(jobs, &match?({n, ""} when n > 0, &1)),
      do: Mix.raise("jobs must be comma-separated positive integers")

    jobs = Enum.map(jobs, &elem(&1, 0))

    if length(jobs) != length(Enum.uniq(jobs)) or length(jobs) < 2,
      do: Mix.raise("select at least two distinct job limits")

    jobs
  end

  defp validate!(opts) do
    unless opts[:lean_threads] > 0 and opts[:max_cases] > 0 and opts[:seed] >= 0 and
             opts[:trials] > 0 and opts[:suite_repetitions] > 0,
           do:
             Mix.raise(
               "threads, max-cases, trials and suite-repetitions must be positive; seed must be nonnegative"
             )

    validate_test_files!(opts[:test_files])
  end

  defp validate_test_files!(selection) do
    if selection do
      files = String.split(selection, ",")

      unless Enum.all?(
               files,
               &(String.starts_with?(Path.expand(&1), Path.expand("test") <> "/") and
                   String.ends_with?(&1, "_test.exs") and File.regular?(&1))
             ),
             do: Mix.raise("test-files must select existing test files inside test/")
    end
  end
end
