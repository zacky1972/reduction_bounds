defmodule ReductionBounds do
  @moduledoc ~S'''
  Verifies Lean declarations and infers symbolic costs for supported list traversals.

  ## Examples

  Run these examples in `iex -S mix` from the project root. Define a
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
      def forward_length(xs), do: list_length(xs)
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

  ### Derive a bound under an input contract

  Continue in the same IEx session, using the compiled `beam` and the
  `~LEAN` sigil from `Lynx.Lean`. This contract admits lists of fewer than
  100 positive integers.
  Positivity is the invariant, and the sum of the entries is the size
  measure. Removing a positive head decreases the measure by at least one.

  ```elixir
  contract = ~LEAN"""
  def inputInvariant (xs : List Int) : Prop := ∀ x ∈ xs, 0 < x
  def inputPrecondition (xs : List Int) : Prop :=
    xs.length < 100 ∧ inputInvariant xs
  def inputSize (xs : List Int) : Nat := (xs.map Int.toNat).sum

  theorem inputInvariantInit (xs : List Int) :
      inputPrecondition xs → inputInvariant xs := by
    intro precondition
    exact precondition.2

  theorem inputInvariantTail (head : Int) (tail : List Int) :
      inputInvariant (head :: tail) → inputInvariant tail := by
    intro invariant x member
    exact invariant x (List.mem_cons_of_mem head member)

  theorem inputSizeTail (head : Int) (tail : List Int) :
      inputInvariant (head :: tail) → inputSize tail + 1 ≤ inputSize (head :: tail) := by
    intro invariant
    have positive := invariant head (by simp)
    simp [inputSize]
    omega
  """

  options = [beam_binaries: [beam], input_contract: contract]
  callee = {SearchDemo, :list_length, 1}

  {:ok, %{size_measure: :input_size, refined_upper_bound: callee_bound}} =
    ReductionBounds.infer_list_bound(callee, options)
  ```

  Lean checks the three contract lemmas and derives that the list length
  is at most the custom measure. In the returned formula, `n` denotes
  `inputSize xs` for inputs satisfying `inputPrecondition xs`. For example,
  `[2, 5, 1]` gives `n = 8`.

  ### Reuse the callee's bound in a wrapper

  Pass the wrapper and callee as separate targets, with the same contract.
  The wrapper forwards its argument unchanged within the same module.

  ```elixir
  caller = {SearchDemo, :forward_length, 1}

  {:ok, %{size_measure: :input_size, upper_bound: {:add, :caller_cost, ^callee_bound}}} =
    ReductionBounds.infer_list_call_bound(caller, callee, options)
  ```

  The pinned pattern checks that the wrapper formula contains the same
  refined bound as the preceding call. `infer_list_call_bound/3` checks the
  callee theorem again and applies it in the same Lean run. `caller_cost`
  represents the wrapper's own symbolic cost.
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
          | {:priv_dir, :bad_name}
          | {:beam_registration, %CompileError{}}

  @type verification_option ::
          {:max_concurrency, pos_integer()}
          | {:timeout, non_neg_integer()}
          | {:beam_binaries, [binary()]}
          | {:termination_suffixes, %{optional(target()) => Lynx.Lean.t()}}
          | {:lean_options, [{atom(), integer() | boolean() | String.t()}]}

  @type verification_result ::
          {:ok, [{target(), target_result()}]} | {:error, setup_error()}

  @type list_inference_option :: verification_option() | {:input_contract, Lynx.Lean.t()}

  @type struct_inference_option ::
          {:max_concurrency, pos_integer()}
          | {:timeout, non_neg_integer()}
          | {:beam_binaries, [binary()]}
          | {:lean_options, [{atom(), integer() | boolean() | String.t()}]}

  @type execution_inference_option ::
          struct_inference_option()
          | {:call_contracts, %{optional(target()) => non_neg_integer()}}

  @type periodic_inference_option ::
          struct_inference_option() | {:periodic_contract, Lynx.Lean.t()}

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
  different maximum step counts of empty-list and early-stop paths. Each
  charge names a clause and an operation. A dispatch
  charge includes the tests that led to the clause. ERTS reduction charges
  are outside this model. Accepts the same options as file-based verification.

  The value_model field identifies a recognized membership, length, reversal,
  or composed model.
  For those models, Lean also proves that the costed model returns the same
  value as the translated target on integer lists and that its cost obeys
  the upper bound. A nil value_model means only the symbolic cost rules
  were checked.

  The target {:lists, :member, 2} uses Lynx's built-in value model for an
  integer key and a proper integer list. Its charges describe the empty,
  hit, and continue cases of the symbolic traversal. In the continue
  case, recursive_call denotes a step to the next list cell in the model.

  The target {:lists, :reverse, 2} uses Lynx's built-in reversal model.
  Both arguments must be proper integer lists. The size measure applies
  to the first argument, and the result is its reversal followed by
  the accumulator. The symbolic bound does not depend on accumulator length.

  The composed model analyzes Core Erlang functions without recursion that
  use static calls, single-value bindings, and Boolean branches. The
  input is a proper integer list, optionally preceded by an integer key.
  When the derivation branches, path_bounds reports separate bounds for
  the first Boolean decision's true and false paths. The upper_bound
  covers both paths. A call_bound names the callee and carries its bound
  specialized to the sizes of the actual arguments.

  For a recognized value model, pass input_contract as a Lean block to
  prove the bounds under an input precondition with a tail invariant and a
  natural-valued size measure. See the module examples.
  """
  @spec infer_list_bound(target(), [list_inference_option()]) :: {:ok, map()} | {:error, term()}
  def infer_list_bound(target, options \\ []) do
    with {:ok, options} <- validate_options(options, :list_bound),
         {:ok, candidate} <- ReductionBounds.ListBound.infer(target, options[:beam_binaries]) do
      {contract, options} = Keyword.pop(options, :input_contract)
      verify_list_candidate(target, candidate, contract, options)
    end
  end

  @doc """
  Infers a symbolic upper bound for one CircularBuffer.insert/2 call.

  The buffer must have proper integer lists and a valid count and capacity,
  and the item must be an integer. The size parameter n is the capacity.
  Lean checks the cost and invariant of the state model for the recognized
  Core Erlang clauses. This analysis uses the list contract for Enum.reverse/1.
  """
  @spec infer_circular_buffer_bound([verification_option()]) :: {:ok, map()} | {:error, term()}
  def infer_circular_buffer_bound(options \\ []) do
    with {:ok, options} <- validate_options(options, :search),
         {:ok, candidate} <- ReductionBounds.CircularBufferBound.infer(options[:beam_binaries]) do
      verify_bound(
        candidate.target,
        candidate,
        ReductionBounds.CircularBufferBound.proof(),
        options
      )
    end
  end

  @doc """
  Infers a symbolic upper bound for consecutive insertions from CircularBuffer.new/1.

  The size parameters m and n denote capacity and number of insertions.
  The cost covers the calls to insert/2 with integer items. Lean verifies
  the exact rotation count for the state model and the resulting cost bound.
  """
  @spec infer_circular_buffer_sequence_bound([verification_option()]) ::
          {:ok, map()} | {:error, term()}
  def infer_circular_buffer_sequence_bound(options \\ []) do
    with {:ok, options} <- validate_options(options, :search),
         {:ok, candidate} <-
           ReductionBounds.CircularBufferSequenceBound.infer(options[:beam_binaries]) do
      verify_bound(
        candidate.target,
        candidate,
        ReductionBounds.CircularBufferSequenceBound.proof(),
        options
      )
    end
  end

  @doc """
  Infers the event count and symbolic cost for repeated calls to a
  counter with fixed progress and a reset at its threshold.

  The target takes a pending count and a period and returns the
  updated pending count and a Boolean event flag. The initial count
  must be below the period. Both are natural numbers and the period
  must be at least the positive increment recovered from the code.

  Pass a Lean block as :periodic_contract to add an invariant and a
  measure for the initial state. Define periodicInvariant and
  periodicMeasure and prove periodicInvariantStep and
  periodicMeasureBounds using periodicDomain and periodicNext.
  The result reports the derived and supplied conditions and includes
  a separate upper bound expressed in the supplied measure.
  """
  @spec infer_periodic_bound(target(), [periodic_inference_option()]) ::
          {:ok, map()} | {:error, term()}
  def infer_periodic_bound(target, options \\ []) do
    with :ok <- validate_targets([target]),
         {:ok, options} <- validate_options(options, :periodic_bound),
         {contract, options} = Keyword.pop(options, :periodic_contract),
         {:ok, candidate, proof} <-
           ReductionBounds.PeriodicBound.infer(target, options[:beam_binaries], contract) do
      verify_bound(target, candidate, proof, Keyword.delete(options, :beam_binaries))
    end
  end

  @doc """
  Infers a symbolic bound for a local wrapper that forwards every argument
  unchanged to a list traversal. The callee must have a recognized value
  model. Lean checks the callee theorem and reuses it to prove the wrapper
  bound, which adds the symbolic caller_cost to the callee's bound.

  An optional input_contract Lean block can supply a precondition, a
  tail invariant, and a size measure. See the module examples.
  """
  @spec infer_list_call_bound(target(), target(), [list_inference_option()]) ::
          {:ok, map()} | {:error, term()}
  def infer_list_call_bound(caller, callee, options \\ []) do
    with {:ok, options} <- validate_options(options, :list_bound),
         :ok <-
           ReductionBounds.ListBound.check_forwarding_call(
             caller,
             callee,
             options[:beam_binaries]
           ),
         {:ok, candidate} <- ReductionBounds.ListBound.infer(callee, options[:beam_binaries]) do
      {contract, options} = Keyword.pop(options, :input_contract)

      with {:ok, proof} <- ReductionBounds.ListBound.forwarding_proof(caller, candidate, contract) do
        result = %{
          target: caller,
          callee: callee,
          metric: :symbolic_cost,
          upper_bound: {:add, :caller_cost, candidate.refined_upper_bound},
          size_measure: list_size_measure(contract)
        }

        verify_bound(caller, result, proof, options)
      end
    end
  end

  defp verify_list_candidate(target, candidate, contract, options) do
    with {:ok, proof} <- ReductionBounds.ListBound.input_proof(candidate, contract) do
      result =
        candidate |> Map.delete(:program) |> Map.put(:size_measure, list_size_measure(contract))

      verify_bound(target, result, proof, options)
    end
  end

  @doc """
  Derives a symbolic cost upper bound for a supported Core Erlang function
  with map or struct operations. Pass the target as a module, function,
  and arity tuple. Use beam_binaries for in-memory modules. The timeout,
  max_concurrency, and lean_options settings match those for verification.

      ReductionBounds.infer_struct_bound({MyCounter, :debit, 2})

  Lean checks the bound for every path in the original fragment's cost
  model. Each opaque path has a separate symbolic cost in the result.
  The result includes the normalized fragment and certificates. For the
  supported unguarded map cases and variable aliases, value_agreement is
  :checked after Lean verifies decoding and normalization from the
  extracted Core fragment. Lean derives the required field facts in
  scope and uses the same interpretation of opaque branches on both
  sides. A value_agreement of :unsupported means Lean checked individual
  rewrite certificates under their listed field assumptions.
  """
  @spec infer_struct_bound(target(), [struct_inference_option()]) ::
          {:ok, map()} | {:error, term()}
  def infer_struct_bound(target, options \\ []) do
    with :ok <- validate_targets([target]),
         {:ok, options} <- validate_options(options, :struct_bound),
         {:ok, candidate, proof} <-
           ReductionBounds.ComposedBound.infer_struct(target, options[:beam_binaries]) do
      verify_bound(target, candidate, proof, Keyword.delete(options, :beam_binaries))
    end
  end

  @doc """
  Checks a symbolic cost bound for every modeled execution of a supported
  unary Core Erlang function.

  The input must be a nonnegative integer. The fragment supports a zero
  clause and a default clause, sequential bindings, zero tests, integer
  addition, static unary calls, and self calls on the input minus one.
  The result gives the zero and successor equations for the upper bound.
  In a successor equation, :previous denotes the bound at the preceding input.

  Supply :call_contracts as a map from static targets to nonnegative
  symbolic cost limits, excluding the caller's own call charge. Each
  contract assumes a natural result and normal termination for reachable
  calls with a natural input. Lean checks the cost bound under the limits
  and proves termination of the modeled target under the totality
  assumptions. A missing contract is reported with the callee's target.
  Unsupported expressions or invalid recursive calls prevent verification.
  """
  @spec infer_verified_bound(target(), [execution_inference_option()]) ::
          {:ok, map()} | {:error, term()}
  def infer_verified_bound(target, options \\ []) do
    with :ok <- validate_targets([target]),
         {:ok, options} <- validate_options(options, :execution_bound),
         {contracts, options} = Keyword.pop!(options, :call_contracts),
         {:ok, candidate, proof} <-
           ReductionBounds.ExecutionBound.infer(target, options[:beam_binaries], contracts) do
      verify_bound(target, candidate, proof, Keyword.delete(options, :beam_binaries))
    end
  end

  defp list_size_measure(nil), do: :list_length
  defp list_size_measure(%Lynx.Lean{}), do: :input_size

  defp verify_bound(target, candidate, proof, options) do
    source = Map.get(candidate, :source, :translated)

    case verify_source(:inline, [target], [postlude: proof] ++ options, source) do
      {:ok, [{^target, {:ok, reports}}]} -> {:ok, Map.put(candidate, :reports, reports)}
      {:ok, [{^target, {:error, reason}}]} -> {:error, reason}
      {:error, _reason} = error -> error
    end
  end

  defp verify_source(source, targets, options, definition \\ :translated) do
    with :ok <- validate_targets(targets),
         {:ok, options} <- validate_options(options, source),
         {:ok, proof, options} <- resolve_proof(source, options),
         {beams, options} = Keyword.pop!(options, :beam_binaries),
         {suffixes, options} = Keyword.pop!(options, :termination_suffixes),
         {:ok, postludes} <- proof_postludes(proof, definition),
         {:ok, translation} <- prepare_translation(postludes, beams, suffixes) do
      {:ok, verify_targets(translation, Enum.uniq(targets), options, definition)}
    end
  end

  defp proof_postludes(proof, :struct_fragment), do: ReductionBounds.ProofInput.postludes(proof)

  defp proof_postludes(proof, :execution_fragment),
    do: ReductionBounds.ProofInput.execution_postludes(proof)

  defp proof_postludes(proof, _definition), do: {:ok, [proof]}

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

    allowed =
      case source do
        :inline ->
          [:postlude | defaults]

        :list_bound ->
          [:input_contract | defaults]

        :struct_bound ->
          Keyword.delete(defaults, :termination_suffixes)

        :execution_bound ->
          [call_contracts: %{}] ++ Keyword.delete(defaults, :termination_suffixes)

        :periodic_bound ->
          [:periodic_contract | Keyword.delete(defaults, :termination_suffixes)]

        _ ->
          defaults
      end

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

  defp valid_option?({:input_contract, value}), do: is_struct(value, Lynx.Lean)
  defp valid_option?({:periodic_contract, value}), do: is_struct(value, Lynx.Lean)
  defp valid_option?({:postlude, value}), do: is_struct(value, Lynx.Lean)
  defp valid_option?({:max_concurrency, value}), do: is_integer(value) and value > 0
  defp valid_option?({:timeout, value}), do: is_integer(value) and value in 0..4_294_967_295

  defp valid_option?({:beam_binaries, values}) do
    is_list(values) and Enum.all?(values, &is_binary/1)
  end

  defp valid_option?({:call_contracts, %{} = contracts}) when not is_struct(contracts) do
    Enum.all?(contracts, fn {target, bound} ->
      valid_target?(target) and is_integer(bound) and bound >= 0
    end)
  end

  defp valid_option?({:call_contracts, _value}), do: false

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

  defp prepare_translation(postludes, beams, suffixes) do
    translation = Lynx.Translation.new(postludes: postludes, termination_suffixes: suffixes)
    {:ok, Enum.reduce(beams, translation, &Lynx.Translation.add(&2, &1))}
  rescue
    error in CompileError -> {:error, {:beam_registration, error}}
  end

  defp verify_targets(_translation, [], _options, _definition), do: []

  defp verify_targets(translation, targets, options, definition) do
    project_dir = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
    {lean_options, task_options} = Keyword.pop!(options, :lean_options)
    {:ok, supervisor} = Task.Supervisor.start_link()

    try do
      supervisor
      |> Task.Supervisor.async_stream_nolink(
        targets,
        fn target ->
          {target, verify_target(target, translation, project_dir, lean_options, definition)}
        end,
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

  defp verify_target(target, translation, project_dir, lean_options, definition) do
    files = assemble_target(translation, target, definition)
    reports = Lynx.Commands.verify!(project_dir, files, options: lean_options)

    if Enum.all?(reports, &(&1.status == :ok)) do
      {:ok, reports}
    else
      {:error, {:verification_failed, reports}}
    end
  rescue
    error -> {:error, {:lynx, error}}
  end

  defp assemble_target(translation, {module, function, arity}, :translated) do
    translation
    |> Lynx.Translation.translate(module, [{function, arity}])
    |> Lynx.Translation.assemble(cache: false)
  end

  defp assemble_target(translation, target, :composed) do
    translation |> assemble_target(target, :translated) |> import_postlude("Erlang.lists")
  end

  defp assemble_target(translation, _target, :circular_buffer_model) do
    translation |> Lynx.Translation.assemble(cache: false) |> import_postlude("Erlang.lists")
  end

  defp assemble_target(translation, _target, :periodic_fragment) do
    Lynx.Translation.assemble(translation, cache: false)
  end

  defp assemble_target(translation, _target, fragment)
       when fragment in [:struct_fragment, :execution_fragment] do
    ReductionBounds.ProofInput.assemble(translation)
  end

  # cspell:words leanj
  defp assemble_target(translation, {module, _, _}, :lynx_builtin) do
    # Lynx's runner resolves this import to its bundled Erlang model.
    import = :lynx_core_to_leanj.module_name(module)
    translation |> Lynx.Translation.assemble(cache: false) |> import_postlude(import)
  end

  defp import_postlude(files, import) do
    for file <- files do
      case file do
        %{"module" => "Erlang.postlude"} ->
          Map.update!(file, "imports", &Enum.uniq([import | &1]))

        _ ->
          file
      end
    end
  end
end
