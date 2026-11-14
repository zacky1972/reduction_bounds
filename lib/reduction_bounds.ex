defmodule ReductionBounds do
  @moduledoc ~S'''
  Verifies Lean declarations and infers symbolic costs for supported list traversals.

  ## Examples

  Run these examples in `iex -S mix` from the project root. Define an
  list search and a list length function, then retain the compiled BEAM binary.

  ```elixir
  import Lynx.Lean

  {:module, SearchDemo, beam, _} =
    defmodule SearchDemo do
      @compile :debug_info

      def contains(_key, []), do: false
      def contains(key, [head | _]) when head === key, do: true
      def contains(key, [_ | tail]), do: contains(key, tail)

      def list_length([]), do: 0
      def list_length([_ | tail]), do: 1 + list_length(tail)
    end

  target = {SearchDemo, :contains, 2}
  ```

  Use `verify/2` with an inline Lean postlude to check that searching an
  empty list returns the Erlang atom `false`.

  ```elixir
  {:ok, [{^target, {:ok, _reports}}]} =
    ReductionBounds.verify([target],
      beam_binaries: [beam],
      postlude: ~LEAN"""
      theorem containsEmpty :
          Elixir.SearchDemo.«contains/2» (.integer 7) .nil = .ok (.atom "false") := by
        rfl
      """
    )
  ```

  Use `infer_search_bound/2` to obtain a bound for the symbolic cost model.

  ```elixir
  {:ok, bound} = ReductionBounds.infer_search_bound(target, beam_binaries: [beam])
  :symbolic_cost = bound.metric
  {:add, {:max, :c_empty, :c_hit}, {:mul, :n, :c_step}} = bound.upper_bound
  ```

  Here, `n` bounds the input list length. The symbolic parameters account
  for an empty list, a hit at the head, and one step that continues with
  the tail. Lean checks the bound on this model. Relating those parameters
  to ERTS reduction charges requires a separate analysis.

  Use `infer_list_bound/2` to apply the same analysis rules to the search
  and the length function.

  ```elixir
  {:ok, search} = ReductionBounds.infer_list_bound(target, beam_binaries: [beam])

  {:ok, length} =
    ReductionBounds.infer_list_bound({SearchDemo, :list_length, 1}, beam_binaries: [beam])

  :symbolic_cost = search.metric
  :symbolic_cost = length.metric

  {:add, base, {:mul, :n, step}} = length.upper_bound
  {:add, {:charge, 0, :dispatch}, {:charge, 0, :value}} = base

  {:add, {:charge, 1, :dispatch},
   {:add, {:charge, 1, :recursive_call}, {:charge, 1, :addition}}} = step
  ```

  The bound for `list_length/1` has the form `base + n * step`. Each
  `{:charge, clause_index, operation}` identifies a symbolic cost by the
  clause's zero-based index and operation. The step includes the addition
  performed after the recursive call returns.

  The `refined_upper_bound` field distinguishes reaching the empty list
  after at most `n` steps from stopping on a nonempty list after at most
  `n - 1` steps. At `n = 0`, only the empty-list cost applies.
  To use the symbolic bound for ERTS reductions, map the compiled paths
  to the modeled charges and justify each charge under the allowed VM
  states for the target build, including the available reduction budget.
  '''

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
          | :missing_postlude
          | {:invalid_option, atom(), term()}
          | {:read_lean, Path.t(), File.posix()}
          | {:beam_registration, %CompileError{}}

  @type verification_option ::
          {:max_concurrency, pos_integer()}
          | {:timeout, non_neg_integer()}
          | {:beam_binaries, [binary()]}
          | {:termination_suffixes, %{optional(target()) => Lynx.Lean.t()}}
          | {:lean_options, [{atom(), integer() | boolean() | String.t()}]}

  @type verification_result ::
          {:ok, [{target(), target_result()}]} | {:error, setup_error()}

  @doc """
  Checks a Lean file or an inline Lean postlude against each target.

  Pass a filename relative to the Mix project's lean/ directory and
  a list of targets, or pass the targets first with a required
  postlude option containing a Lynx.Lean value, such as one produced
  by the ~LEAN sigil. Target tuples have the form {module, function, arity}.
  """
  @spec verify(Path.t(), [target()]) :: verification_result()
  @spec verify([target()], [verification_option() | {:postlude, Lynx.Lean.t()}]) ::
          verification_result()
  def verify(targets, options) when is_list(targets) do
    verify_source(:inline, targets, options)
  end

  def verify(lean_file, targets), do: verify(lean_file, targets, [])

  @doc """
  Checks a Lean file against each target independently.

  Give a filename relative to the current Mix project's lean/ directory
  and a list of {module, function, arity} tuples. The file is loaded as a
  Lynx postlude in each verification, so it must elaborate with the
  definitions available for that target. Target modules are resolved
  from registered BEAM binaries or through the BEAM code path.

  Options

    * beam_binaries (default []) registers BEAM binaries for target
      modules and dependencies in this invocation. The binaries must
      contain debug information from which Lynx can obtain Core Erlang.
      If several binaries define the same module, the last one is used.
      Registration failures are returned before verification starts.

    * termination_suffixes (default %{}) attaches Lean termination
      declarations to translated functions, keyed by {module, function,
      arity}. A suffix can specify how Lean handles a function that may
      diverge on some inputs. Each supplied function must be translated
      in every verification job.
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
  @spec verify(Path.t(), [target()], [verification_option()]) :: verification_result()
  def verify(lean_file, targets, options) do
    verify_source({:file, lean_file}, targets, options)
  end

  @doc """
  Derives a symbolic cost bound for a two-argument integer list search.

  The supported function returns false for an empty list, returns true
  when the head strictly equals the key, and otherwise calls itself with
  the same key and the tail. The input size n bounds the list length.
  The three branch costs are nonnegative symbolic parameters.

  The result includes the recurrence, the bound expression, and Lean
  verification reports for the cost model. ERTS reduction charges are
  outside this model. Accepts the same options as file-based verification.
  """
  @spec infer_search_bound(target(), [verification_option()]) ::
          {:ok, map()} | {:error, term()}
  def infer_search_bound(target, options \\ []) do
    with {:ok, options} <- validate_options(options, :search),
         {:ok, candidate} <- ReductionBounds.SearchBound.infer(target, options[:beam_binaries]) do
      verify_bound(target, candidate, ReductionBounds.SearchBound.proof(), options)
    end
  end

  @doc """
  Infers a symbolic cost bound for a supported traversal of an integer list.

  The traversal may take a key before the list and may test for equality.
  The analysis handles clause dispatch, values, integer addition, sequential
  bindings, and at most one self-call on the tail per branch.

  Results include the branch recurrence and two Lean-checked upper bounds
  for its cost model. The refined_upper_bound field accounts for the
  different maximum step counts of empty-list and early-stop paths. Each charge names a clause and an operation. A dispatch
  charge includes the tests that led to the clause. ERTS reduction charges
  are outside this model. Accepts the same options as file-based verification.

  The value_model field identifies a recognized membership or length model.
  For those models, Lean also proves that the costed model returns the same
  value as the translated target on integer lists and that its cost obeys
  the upper bound. A nil value_model means only the symbolic cost rules
  were checked.
  """
  @spec infer_list_bound(target(), [verification_option()]) :: {:ok, map()} | {:error, term()}
  def infer_list_bound(target, options \\ []) do
    with {:ok, options} <- validate_options(options, :search),
         {:ok, candidate} <- ReductionBounds.ListBound.infer(target, options[:beam_binaries]) do
      verify_bound(target, candidate, ReductionBounds.ListBound.proof(candidate), options)
    end
  end

  defp verify_bound(target, candidate, proof, options) do
    case verify([target], [postlude: proof] ++ options) do
      {:ok, [{^target, {:ok, reports}}]} -> {:ok, Map.put(candidate, :reports, reports)}
      {:ok, [{^target, {:error, reason}}]} -> {:error, reason}
      {:error, _reason} = error -> error
    end
  end

  defp verify_source(source, targets, options) do
    with :ok <- validate_targets(targets),
         {:ok, options} <- validate_options(options, source),
         {:ok, proof, options} <- resolve_proof(source, options),
         {beams, options} = Keyword.pop!(options, :beam_binaries),
         {suffixes, options} = Keyword.pop!(options, :termination_suffixes),
         {:ok, translation} <- prepare_translation(proof, beams, suffixes) do
      {:ok, verify_targets(translation, Enum.uniq(targets), options)}
    end
  end

  defp resolve_proof(:inline, options) do
    case Keyword.pop(options, :postlude) do
      {nil, _options} -> {:error, :missing_postlude}
      {proof, options} -> {:ok, proof, options}
    end
  end

  defp resolve_proof({:file, lean_file}, options) do
    with {:ok, proof} <- read_proof(lean_file) do
      {:ok, proof, options}
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

  defp validate_options(options, source) do
    defaults = [
      max_concurrency: 2,
      timeout: 60_000,
      lean_options: [],
      beam_binaries: [],
      termination_suffixes: %{}
    ]

    allowed = if source == :inline, do: [:postlude | defaults], else: defaults

    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, allowed),
         nil <- Enum.find(options, fn option -> not valid_option?(option) end) do
      {:ok, options}
    else
      false -> {:error, :invalid_options}
      {:error, _keys} -> {:error, :invalid_options}
      {key, value} -> {:error, {:invalid_option, key, value}}
    end
  end

  defp valid_option?({:postlude, value}), do: is_struct(value, Lynx.Lean)
  defp valid_option?({:max_concurrency, value}), do: is_integer(value) and value > 0
  defp valid_option?({:timeout, value}), do: is_integer(value) and value in 0..4_294_967_295

  defp valid_option?({:beam_binaries, values}) do
    is_list(values) and Enum.all?(values, &is_binary/1)
  end

  defp valid_option?({:termination_suffixes, %{} = suffixes}) when not is_struct(suffixes) do
    Enum.all?(suffixes, fn {target, source} ->
      valid_target?(target) and is_struct(source, Lynx.Lean)
    end)
  end

  defp valid_option?({:termination_suffixes, _value}), do: false

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

  defp prepare_translation(proof, beams, suffixes) do
    translation = Lynx.Translation.new(postludes: [proof], termination_suffixes: suffixes)
    {:ok, Enum.reduce(beams, translation, &Lynx.Translation.add(&2, &1))}
  rescue
    error in CompileError -> {:error, {:beam_registration, error}}
  end

  defp verify_targets(_translation, [], _options), do: []

  defp verify_targets(translation, targets, options) do
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
