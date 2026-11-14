defmodule ReductionBounds do
  @moduledoc """
  Verifies Lean declarations against functions translated by Lynx.
  """

  @type target :: {module(), atom(), arity()}
  @type target_result ::
          {:ok, [Lynx.Laws.report()]}
          | {:error,
             {:verification_failed, [Lynx.Laws.report()]}
             | {:lynx, Exception.t()}
             | :timeout
             | {:task_exit, term()}}
  @type setup_error ::
          :no_mix_project
          | :invalid_lean_path
          | {:expected_target_list, term()}
          | {:invalid_targets, [term()]}
          | :invalid_options
          | {:invalid_option, atom(), term()}
          | {:read_lean, Path.t(), File.posix()}

  @type verification_option ::
          {:max_concurrency, pos_integer()}
          | {:timeout, non_neg_integer()}
          | {:lean_options, [{atom(), integer() | boolean() | String.t()}]}

  @doc """
  Checks a Lean file against each target independently.

  Give a filename relative to the current Mix project's lean/ directory
  and a list of {module, function, arity} tuples. The file is loaded as a
  Lynx postlude in each verification, so it must elaborate with the
  definitions available for that target. Target modules are resolved
  through the BEAM code path.

  Options

    * max_concurrency (default 2) limits the number of concurrent tasks
      in this invocation. Set it to 1 for sequential verification.
    * timeout (default 60,000 milliseconds) limits each task from
      translation through Lean verification. A timed-out task is killed
      and reported as {:error, :timeout}. This limits the caller's wait.
      Termination of the external Lake/Lean process tree is outside
      the timeout's guarantee.
    * lean_options (default []) passes options such as maxHeartbeats
      and maxRecDepth to the Lean runner.

  Each target is verified once. Results follow the order in which
  targets first appear. Lynx checks that the module can be translated and
  that the function exists in it. Translation, runner, and task failures
  are reported for the affected target. Malformed values produce
  {:invalid_targets, values} before verification starts. Each offending
  value is listed once in input order.
  This function checks the supplied declarations. It does not derive bounds
  or apply Lynx's law-specific axiom audit to postlude declarations.
  """
  @spec verify(Path.t(), [target()], [verification_option()]) ::
          {:ok, [{target(), target_result()}]} | {:error, setup_error()}
  def verify(lean_file, targets, options \\ []) do
    with :ok <- validate_targets(targets),
         {:ok, options} <- validate_options(options),
         {:ok, proof} <- read_proof(lean_file) do
      {:ok, verify_targets(proof, Enum.uniq(targets), options)}
    end
  end

  defp validate_targets(targets) when is_list(targets) do
    case targets |> Enum.reject(&valid_target?/1) |> Enum.uniq() do
      [] -> :ok
      invalid -> {:error, {:invalid_targets, invalid}}
    end
  end

  defp validate_targets(targets), do: {:error, {:expected_target_list, targets}}

  defp valid_target?({module, function, arity}) do
    is_atom(module) and is_atom(function) and arity in 0..255
  end

  defp valid_target?(_target), do: false

  defp validate_options(options) do
    defaults = [max_concurrency: 2, timeout: 60_000, lean_options: []]

    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, defaults),
         nil <- Enum.find(options, fn option -> not valid_option?(option) end) do
      {:ok, options}
    else
      false -> {:error, :invalid_options}
      {:error, _keys} -> {:error, :invalid_options}
      {key, value} -> {:error, {:invalid_option, key, value}}
    end
  end

  defp valid_option?({:max_concurrency, value}), do: is_integer(value) and value > 0
  defp valid_option?({:timeout, value}), do: is_integer(value) and value in 0..4_294_967_295

  defp valid_option?({:lean_options, values}) do
    Keyword.keyword?(values) and
      Enum.all?(values, fn {_name, value} ->
        is_integer(value) or is_boolean(value) or is_binary(value)
      end)
  end

  defp read_proof(lean_file) when is_binary(lean_file) and byte_size(lean_file) > 0 do
    case Mix.Project.project_file() do
      nil ->
        {:error, :no_mix_project}

      project_file ->
        lean_dir = Path.join(Path.dirname(Path.expand(project_file)), "lean")
        read_proof_in(lean_file, lean_dir)
    end
  end

  defp read_proof(_lean_file), do: {:error, :invalid_lean_path}

  defp read_proof_in(lean_file, lean_dir) do
    case Path.safe_relative(lean_file, lean_dir) do
      {:ok, relative_path} ->
        read_lean_file(Path.join(lean_dir, relative_path))

      :error ->
        {:error, :invalid_lean_path}
    end
  end

  defp read_lean_file(path) do
    case File.read(path) do
      {:ok, source} ->
        {:ok, %Lynx.Lean{source: source, file: path, span: {1, 1}, indentation: 0}}

      {:error, reason} ->
        {:error, {:read_lean, path, reason}}
    end
  end

  defp verify_targets(_proof, [], _options), do: []

  defp verify_targets(proof, targets, options) do
    translation = Lynx.Translation.new(postludes: [proof])
    project_dir = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
    {lean_options, task_options} = Keyword.pop!(options, :lean_options)
    {:ok, supervisor} = Task.Supervisor.start_link()

    try do
      supervisor
      |> Task.Supervisor.async_stream_nolink(
        targets,
        fn target -> {target, verify_target(target, translation, project_dir, lean_options)} end,
        task_options ++ [on_timeout: :kill_task, zip_input_on_exit: true]
      )
      |> Enum.map(fn
        {:ok, result} -> result
        {:exit, {target, :timeout}} -> {target, {:error, :timeout}}
        {:exit, {target, reason}} -> {target, {:error, {:task_exit, reason}}}
      end)
    after
      Supervisor.stop(supervisor)
    end
  end

  defp verify_target({module, function, arity}, translation, project_dir, lean_options) do
    files =
      translation
      |> Lynx.Translation.translate(module, [{function, arity}])
      |> Lynx.Translation.assemble(cache: false)

    reports = Lynx.Commands.verify!(project_dir, files, options: lean_options)

    if Enum.all?(reports, &(&1.status == :ok)) do
      {:ok, reports}
    else
      {:error, {:verification_failed, reports}}
    end
  rescue
    error -> {:error, {:lynx, error}}
  end
end
