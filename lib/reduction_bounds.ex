defmodule ReductionBounds do
  @moduledoc ~S'''
  Verifies Lean declarations and infers symbolic costs and integer sizes for supported code.

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
  def inputInvariant (xs : List Int) : Prop := ∀ x ∈ xs, x > 0
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

  ## Inspect integer ranges and intermediate widths

  Define an integer function and retain its BEAM binary, then supply an
  independent size description for each argument.

  ```elixir
  alias ReductionBounds.IntegerSize

  {:module, SizeDemo, integer_beam, _} =
    defmodule SizeDemo do
      def update(x) do
        y = x * 3
        if y < 0, do: y - 1, else: y + 1
      end
    end

  {:ok, sizes} =
    ReductionBounds.infer_integer_sizes({SizeDemo, :update, 1},
      beam_binaries: [integer_beam],
      input_sizes: [%IntegerSize{lower: -2, upper: 4, magnitude_bits: 3}]
    )

  sizes.result_size
  #=> %IntegerSize{lower: -7, upper: 13, magnitude_bits: 6}
  sizes.intermediates
  sizes.unresolved_sizes
  ```

  Lean checks the final and intermediate descriptions against the shared
  integer interpreter and proves its size rule under the input conditions.
  Branch rows expose the conditions used to narrow their descriptions.
  Unknown widths appear in `unresolved_sizes`. This is a non-recursive
  mathematical integer model: the source decoder remains trusted, agreement
  with a Lynx-translated target is not checked, and no runtime cost bound
  is asserted. See `infer_integer_sizes/2` for the supported fragment.

  ## Derive costs from integer sizes

  The following example includes a growing accumulator. Supply a finite range
  for the initial counter and retain the compiled BEAM binary.

  ```elixir
  {:module, IntegerCostDemo, cost_beam, _} =
    defmodule IntegerCostDemo do
      def sum(counter, accumulator) do
        if counter > 0,
          do: sum(counter - 1, accumulator + counter),
          else: accumulator
      end

      def triple(x), do: x * 3
      def caller(x), do: __MODULE__.triple(x) + 1
    end

  alias ReductionBounds.IntegerSize

  {:ok, sum_bound} =
    ReductionBounds.infer_integer_cost_bound({IntegerCostDemo, :sum, 2},
      beam_binaries: [cost_beam],
      input_sizes: [
        %IntegerSize{lower: 0, upper: 4, magnitude_bits: 3},
        IntegerSize.from_integer(0)
      ]
    )

  sum_bound.result_size
  #=> %IntegerSize{lower: 0, upper: 10, magnitude_bits: 7}
  sum_bound.upper_bound
  sum_bound.conditions.inferred_recursive_inputs

  input = %IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}
  {:ok, triple_bound} =
    ReductionBounds.infer_integer_cost_bound({IntegerCostDemo, :triple, 1},
      beam_binaries: [cost_beam], input_sizes: [input])
  {:ok, caller_bound} =
    ReductionBounds.infer_integer_cost_bound({IntegerCostDemo, :caller, 1},
      beam_binaries: [cost_beam], input_sizes: [input],
      call_contracts: %{{IntegerCostDemo, :triple, 1} => triple_bound})
  caller_bound.conditions.calls
  ```

  A leaf `{:cost, :addition, [a, b]}` means the symbolic addition cost
  evaluated at magnitude bounds `a` and `b`. Sequential work uses `:add`,
  and alternatives use `:max`. All cost functions must be nondecreasing
  in their size parameters. Shift and mask leaves use the constant amount
  or width as their second parameter. The result is not an ERTS reduction
  count or an execution-time guarantee.

  For a modeled external unary call, supply a contract with `input_size`,
  `result_size`, and `upper_bound` instead of a checked result. These are
  assumptions about the normally returning external model. For example:

  ```elixir
  absolute_contract = %{
    input_size: input,
    result_size: %IntegerSize{lower: 0, upper: 4, magnitude_bits: 3},
    upper_bound: {:cost, :absolute, [3, 0]}
  }
  # Pass call_contracts: %{{:erlang, :abs, 1} => absolute_contract} to a caller.
  ```

  For a recursive CRC-style function that masks the accumulator to eight
  bits after each update, an optional invariant can be supplied as:

  ```elixir
  recursive_invariant = [
    %IntegerSize{lower: 0, upper: 4},
    %IntegerSize{lower: 0, upper: 255, magnitude_bits: 8}
  ]
  ```

  Pass it as `recursive_invariant: recursive_invariant` alongside the
  initial input descriptions. The result distinguishes this supplied
  condition from the automatically inferred argument descriptions.
  Lean checks the invariant at every recursive call in the derivation.
  Exhausting `max_unfolding` or `max_nodes` reports an error; neither
  setting is an assumption that recursion terminates.

  ## Identify an operation cost contract

  Use a `CostContract` to label the cost unit and operation-cost declaration.
  This is separate from the contracts for calls to other functions.

  ```elixir
  alias ReductionBounds.CostContract

  {:ok, contract} = CostContract.new(id: :analysis, cost_unit: :symbolic_work)

  {:ok, declared_bound} =
    ReductionBounds.infer_integer_cost_bound({IntegerCostDemo, :triple, 1},
      beam_binaries: [cost_beam],
      input_sizes: [input],
      cost_contract: contract
    )

  declared_bound.cost_contract.id
  #=> :analysis
  declared_bound.applicability.parameters.mask
  #=> {:input_magnitude_bits, :mask_width}
  declared_bound.applicability.contract_instantiation
  #=> :not_checked
  ```

  A declaration may also contain natural-valued expressions; see
  `ReductionBounds.CostContract`. The current Lean proof remains parametric
  in nondecreasing cost functions. Recording or evaluating a declaration does
  not check a concrete instantiation or a comparison between contracts.
  Labels such as `:jit` do not establish correspondence with that runtime.
  To check declarative function and budget ordering separately, use
  `compare_cost_contracts/3`. That check does not transfer the target's bound.

  ## Compare operation cost contracts

  Compare two declarative contracts in the smaller-to-larger direction.
  This example needs no target module or BEAM binary.

  ```elixir
  alias ReductionBounds.CostContract

  functions_a = Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
  functions_b = Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
  {:ok, a} = CostContract.new(id: :a, functions: functions_a)
  {:ok, b} = CostContract.new(id: :b, functions: functions_b)

  {:ok, comparison} =
    ReductionBounds.compare_cost_contracts(a, b,
      budget: {:add, {:cost, :addition, [8, 9]}, {:cost, :binding, [0, 0]}}
    )

  comparison.budget_values
  #=> %{smaller: 10, larger: 12}
  comparison.checked_theorems
  comparison.bound_transfer
  #=> :not_checked
  ```

  Lean checks the ordering for all natural parameters and every composed
  budget. The optional budget's evaluations are also checked. An unresolved
  structural comparison is not a proof that the inequality is false.
  A conditional theorem also compares finite executions of the same integer
  program, preserving the returned value. Its assumptions require every static
  call to have an admitted argument, matching returned values, and ordered actual
  costs. These assumptions are recorded in `execution_conditions`; they are not
  discharged for a target by this API. Use `transfer_integer_bound/3` to
  recheck a target bound and apply the comparison under explicit call conditions.

  ## Transfer an integer bound

  Pass an integer bound carrying a concrete source `cost_contract`, together
  with a smaller destination contract:

  ```elixir
  {:ok, transferred} = ReductionBounds.transfer_integer_bound(bound, destination)
  transferred.upper_bound_contract
  transferred.upper_bound_value
  transferred.checked_theorems
  ```

  The target and any reused callee bounds are analyzed again and both proofs
  are rechecked. The numeric bound is evaluated under the source contract.
  `input_sizes` may narrow the original input domains. For contracted calls,
  supply `callee_correspondence: :shared` for a common mathematical external
  model, or a Lean proof of the two external models' value and actual-cost
  correspondence. Source call contracts remain explicit assumptions.


  ## Verification scope and diagnostics

  Successful contract comparison and integer bound transfer include
  `verification_scope`. Its `checked` field lists completed checks;
  `assumptions` records conditions required by the theorem; `trusted` names
  processing outside the Lean proof; and `unverified` identifies remaining
  claims, including concrete runtime correspondence and wall-clock timing.
  `checked_theorems` remains the list of audited Lean declarations.

  Comparison reports the contracts as `smaller` and `larger`. Transfer
  reports `from` (the source contract B) and `to` (the destination A).
  Input conditions and callee assumptions must hold before applying the
  mathematical guarantee. A checked result does not certify an ERTS build.

  These two APIs report unknown options as `{:error, {:unknown_options, keys}}`.
  Invalid values retain `{:error, {:invalid_option, name, value}}`. Comparison
  accepts `budget`, `timeout`, `max_concurrency`, and `lean_options`; it does
  not accept `beam_binaries` because it selects no target. Transfer accepts
  `beam_binaries` to repeat source extraction. Other diagnostics, such as
  `unresolved_cost_order`, `insufficient_transfer_inputs`, and
  `unresolved_callee_correspondence`, remain errors rather than successful
  transfers. Lean proof or axiom-audit failures report `verification_failed`.

  Reproduce the public workflow examples and rejection checks with:

  ```sh
  REDUCTION_BOUNDS_REPORT=1 mix test --only cost_contract_workflow --trace
  ```

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

  @doc """
  Infers integer ranges and magnitude widths from a supported Core Erlang function.

  The non-recursive fragment supports integer constants and variables, bindings,
  addition, subtraction, multiplication, XOR, constant nonnegative shifts,
  low-bit masks, and Boolean cases comparing an integer expression with a constant.
  All arguments and results are mathematical integers. Input descriptions are
  independent; relational input assumptions are not supported.

  Pass `input_sizes: [size, ...]` in argument order. Omission uses unknown sizes.
  `beam_binaries` supports modules compiled in memory. Other verification options
  include `timeout`, `max_concurrency`, and `lean_options`.

  ```elixir
  alias ReductionBounds.IntegerSize

  {:module, SizeExample, beam, _} =
    defmodule SizeExample do
      def update(x) do
        y = x * 3
        if y < 0, do: y - 1, else: y + 1
      end
    end

  ReductionBounds.infer_integer_sizes({SizeExample, :update, 1},
    beam_binaries: [beam],
    input_sizes: [%IntegerSize{lower: -2, upper: 4, magnitude_bits: 3}]
  )
  ```

  The result contains `result_size`, `intermediates`, branch conditions, and
  `unresolved_sizes`. Lean checks the candidate against the abstract interpreter
  and proves that every evaluation of the reified fragment satisfies the result
  description under the input conditions. Source extraction and reification are
  trusted. `proof_scope: :reified_integer_fragment` and `value_agreement:
  :not_checked` distinguish this from agreement with a Lynx-translated target.
  This entry point derives sizes, not reduction or execution-time bounds.
  Calls outside the fragment and unsupported conditions return contextual errors.
  """
  @spec infer_integer_sizes(target(), keyword()) :: {:ok, map()} | {:error, term()}
  def infer_integer_sizes(target, options \\ []) do
    with :ok <- validate_targets([target]),
         {:ok, options} <- validate_options(options, :integer_sizes),
         {inputs, options} = Keyword.pop!(options, :input_sizes),
         {:ok, candidate, proof} <-
           ReductionBounds.IntegerAnalysis.infer(target, options[:beam_binaries], inputs) do
      verify_bound(target, candidate, proof, Keyword.delete(options, :beam_binaries))
    end
  end

  @doc """
  Derives a size-dependent symbolic cost bound for the supported Core Erlang integer fragment.

  Supply independent `input_sizes` in argument order. Operation costs remain
  arbitrary natural-valued functions nondecreasing in their size parameters.
  The result records `result_size`, `upper_bound`, `intermediates`, and `conditions`.
  This is a symbolic model, with no ERTS reduction or timing claim.

  The optional `cost_contract` is a `ReductionBounds.CostContract` declaration
  identifying operation costs, the cost unit, and the integer semantics profile.
  Omission records the existing symbolic contract. The result's `cost_contract`
  and `applicability` fields identify the declaration, parameter meanings,
  input domains, recursive conditions, and callee assumptions actually used.
  This operation contract is separate from a callee's `call_contracts` entry.

  Declarative cost functions can be recorded and evaluated in Elixir. The Lean
  bound remains quantified over arbitrary nondecreasing cost functions;
  `applicability.contract_instantiation: :not_checked` means a concrete
  declaration has not been instantiated and checked in Lean. A contract named
  `:jit` does not establish JIT applicability. Runtime correspondence remains
  `:not_checked`, and comparisons and bound transfers between contracts are
  not implemented by this option.

  ```elixir
  alias ReductionBounds.CostContract

  {:ok, contract} = CostContract.new(id: :analysis, cost_unit: :symbolic_work)

  {:ok, bound} =
    ReductionBounds.infer_integer_cost_bound({MyModule, :sum, 2},
      input_sizes: [
        %ReductionBounds.IntegerSize{lower: 0, upper: 4, magnitude_bits: 3},
        ReductionBounds.IntegerSize.from_integer(0)
      ],
      cost_contract: contract
    )

  bound.applicability.parameters.shift_left
  # {:input_magnitude_bits, :shift_amount}
  ```

  Static unary calls use `call_contracts`, keyed by module, function, and arity.
  Each contract has `input_size`, `result_size`, and `upper_bound`. A checked
  result from this API for a unary function can instead
  be supplied directly; its derivation is checked again. External call models
  must return normally and obey the supplied contracts.

  Two-argument self recursion is expanded into a finite derivation under the
  supplied input ranges. `max_unfolding` (default 32) limits nested self calls;
  `max_nodes` (default 10_000) limits analysis nodes. Exhaustion is an error,
  never a termination assumption. An optional two-element `recursive_invariant`
  is checked at entry and at every reachable self call.

  Lean checks the derivation, intermediate summaries, source lowering certificate,
  and any supplied invariant. It proves the cost bound for every modeled run
  and constructs a finite normal run under the call contracts. Source agreement
  is with the reified supported Core fragment and its stated mathematical
  primitive semantics. BEAM extraction and reification remain trusted.

      ReductionBounds.infer_integer_cost_bound({MyModule, :sum, 2},
        input_sizes: [
          %ReductionBounds.IntegerSize{lower: 0, upper: 4, magnitude_bits: 3},
          ReductionBounds.IntegerSize.from_integer(0)
        ]
      )

  Unknown operand widths, missing or inapplicable contracts, unsupported syntax,
  failed invariants, and unresolved recursion produce contextual errors.
  `beam_binaries`, `lean_options`, `timeout`, and `max_concurrency` work as for
  the other verification APIs.
  """
  @spec infer_integer_cost_bound(target(), keyword()) :: {:ok, map()} | {:error, term()}
  def infer_integer_cost_bound(target, options \\ []) do
    with :ok <- validate_targets([target]),
         {:ok, options} <- validate_options(options, :integer_cost),
         {:ok, candidate, proof} <- ReductionBounds.IntegerCostBound.infer(target, options) do
      verification = Keyword.take(options, [:max_concurrency, :timeout, :lean_options])
      verify_bound(target, candidate, proof, verification)
    end
  end

  @doc """
  Checks pointwise ordering of two declarative operation cost contracts in Lean.

  Arguments are ordered from smaller to larger. The contracts must share the
  cost unit, semantics, event profile, and parameter meanings. Both must have
  declarative functions. The comparison is universal over natural parameters,
  using a conservative structural certificate; an unresolved comparison is
  not a proof that the inequality is false.

  Lean checks expression monotonicity, each operation's ordering, and ordering
  of every existing symbolic budget under the two function assignments.
  Optionally pass `budget: bound.upper_bound` to check its two evaluations.
  Auxiliary callee cost names must be declared on both sides.

  Lean also checks a generic execution comparison for the existing integer
  semantics: for the same program and input, every admitted finite execution
  under the smaller assignment has a same-value execution under the larger
  assignment with at least its cost. This covers bindings, arithmetic, branches,
  static calls, and finite recursion. It needs neither a VM model nor a new
  definition of program execution.

  Static calls require explicit value agreement and actual-cost ordering on
  their admitted input domains. Ordered callee budgets alone are insufficient.
  The existing size derivation can establish that each call's argument meets
  its input contract; the theorem retains the assumptions needed by that derivation.

  The result records `proof_scope: :cost_functions_budgets_and_executions`,
  `execution_cost_order: :checked`, and the required `execution_conditions`.
  This checks the conditional generic theorem without selecting a target or
  proving that its callees meet those conditions. Accordingly,
  `execution_applicability` is `:not_checked` and `callee_correspondence` is
  `:assumed`. No caller-supplied label counts as evidence for these assumptions.
  This comparison alone leaves bound transfer and concrete integer contract
  instantiation unchecked; `transfer_integer_bound/3` performs those checks
  separately. Correspondence with an ERTS implementation remains unchecked.

  ```elixir
  alias ReductionBounds.CostContract

  smaller_functions = Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
  larger_functions = Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
  {:ok, smaller} = CostContract.new(id: :smaller, functions: smaller_functions)
  {:ok, larger} = CostContract.new(id: :larger, functions: larger_functions)

  {:ok, comparison} =
    ReductionBounds.compare_cost_contracts(smaller, larger,
      budget: {:add, {:cost, :addition, [8, 9]}, {:cost, :binding, [0, 0]}}
    )

  comparison.budget_values
  #=> %{smaller: 10, larger: 12}
  ```

  `verification_scope` separates the conditional theorem from its assumptions,
  trusted metadata and serialization, and unverified target or runtime applicability.
  `timeout`, `max_concurrency`, and `lean_options` work as for verification.
  Unknown options, including `beam_binaries`, report `unknown_options`.
  """
  @spec compare_cost_contracts(
          ReductionBounds.CostContract.t(),
          ReductionBounds.CostContract.t(),
          keyword()
        ) ::
          {:ok, map()} | {:error, term()}
  def compare_cost_contracts(smaller, larger, options \\ []) do
    with {:ok, options} <- validate_options(options, :cost_comparison),
         {:ok, candidate, proof} <-
           ReductionBounds.ContractComparison.infer(smaller, larger, options[:budget]) do
      verification = Keyword.take(options, [:max_concurrency, :timeout, :lean_options])
      verify_bound({__MODULE__, :compare_cost_contracts, 3}, candidate, proof, verification)
    end
  end

  @doc """
  Rechecks an integer bound and transfers it to a smaller operation-cost contract.

  Pass a result of `infer_integer_cost_bound/2` whose `cost_contract` contains
  concrete declarative functions. The source contract belongs to `bound`;
  `destination` is the smaller contract. The target and any reused callees are
  extracted again from BEAM. Stored derivations, formulas, and translation
  certificates must match fresh analysis, and both proofs are checked again in Lean.
  Result flags such as `checked_theorems` are not accepted as proof evidence.

  The reused formula is evaluated under the source contract. The result's
  `upper_bound_contract` identifies that contract and `upper_bound_value` is
  the checked numeric bound. Do not evaluate the formula under the destination
  contract and assume that smaller value is also a bound.

  `input_sizes` may retain or narrow the original input domains. Lean checks
  coverage of the original precondition. Recursive invariants and call contracts
  remain those of the original derivation. `max_unfolding`, `max_nodes`,
  `beam_binaries`, and the standard verification options are supported.

  When call contracts are present, supply `callee_correspondence: :shared` to
  state that both mathematical executions use the same external value-and-cost
  model. Without this choice or a Lean proof, transfer reports an unresolved
  callee correspondence. This is not a claim about two concrete runtime modes.

  Alternatively, pass a `Lynx.Lean` block as `callee_correspondence`. It must
  define `transferExternalA`, `transferExternalB`, and prove
  `transferCalleeAgreement`, with type:

  ```lean
  ReductionBounds.BoundTransfer.ExternalAgreement
    (fun key argument => (SourceBound.costContracts key).input.Holds argument)
    transferExternalA transferExternalB
  ```

  A denotes the destination and B the source. The proof must establish equal
  values and ordered actual callee costs on the source input contracts.
  Source callee output and cost contracts remain explicit assumptions of the
  generated theorem. Their smaller-contract budgets are not assumed to hold.

  ```elixir
  alias ReductionBounds.{CostContract, IntegerSize}

  functions = Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
  {:ok, source} = CostContract.new(id: :source, functions: functions)
  functions = Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
  {:ok, destination} = CostContract.new(id: :destination, functions: functions)

  {:ok, bound} =
    ReductionBounds.infer_integer_cost_bound({MyModule, :square, 1},
      input_sizes: [%IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}],
      cost_contract: source
    )

  {:ok, transferred} = ReductionBounds.transfer_integer_bound(bound, destination)
  transferred.upper_bound_value
  transferred.upper_bound_contract
  #=> :source
  ```

  The generated theorem bounds every destination execution covered by the
  preconditions. Its termination theorem retains the finite derivation and
  normally returning source callee assumptions. Concrete runtime correspondence
  remains `:not_checked`. The returned `verification_scope` records these
  assumptions, the checked steps, and the trusted extraction and serialization.
  Unknown option names report `unknown_options`.
  """
  @spec transfer_integer_bound(map(), ReductionBounds.CostContract.t(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def transfer_integer_bound(bound, destination, options \\ []) do
    with {:ok, options} <- validate_options(options, :bound_transfer),
         {:ok, candidate, proof} <-
           ReductionBounds.BoundTransfer.infer(bound, destination, options) do
      verification = Keyword.take(options, [:max_concurrency, :timeout, :lean_options])
      verify_bound(candidate.target, candidate, proof, verification)
    end
  end

  defp list_size_measure(nil), do: :list_length
  defp list_size_measure(%Lynx.Lean{}), do: :input_size

  @doc """
  Verifies supplied Port-model traces, universal cost safety and optional completion conditions.

  `events` accepts registered event names or protocol event structs. Supply
  `observations: %{index => observation}` from `ProtocolConditions.observe/2`.
  Optional `completion: [limits: ..., progress: ..., goal: :termination]`
  declares the earlier model's completion conditions. Missing progress keeps
  a checked cost bound and reports diagnostics; it does not establish completion.

  The result reports `verification_scope`, `checked_theorems`, assumptions,
  trusted processing and unresolved obligations. Conditional completion is
  scoped to the supplied model. This API does not analyze a target function.
  See the Port interactions guide under the examples documentation.

  ```elixir
  names = [:prepare, :submit_accepted]
  {:ok, observation} = ReductionBounds.ProtocolConditions.observe(%{request: []})
  observations = %{0 => observation, 1 => observation}
  {:ok, result} = ReductionBounds.verify_port_model(profile, names, observations: observations)
  result.verification_scope.kind
  #=> :supplied_port_model
  result.completion.theorem_status
  #=> :not_established
  ```

  Construct `profile` with `PortProtocol.conditions/1` and `ProtocolCost.new/2`;
  the examples guide supplies the complete size, count and cost declarations.
  """
  @spec verify_port_model(ReductionBounds.ProtocolCost.t(), list(), keyword()) ::
          {:ok, map()} | {:error, term()}
  def verify_port_model(profile, events, options \\ []) do
    with {:ok, options} <- validate_options(options, :port_model),
         {observations, options} = Keyword.pop!(options, :observations),
         {completion, options} = Keyword.pop!(options, :completion),
         {:ok, candidate, proof} <-
           ReductionBounds.PortWorkflow.build(profile, events, observations, completion),
         {:ok, result} <-
           verify_bound({__MODULE__, :verify_port_model, 3}, candidate, proof, options) do
      ReductionBounds.PortResult.verified(result, result.reports)
    end
  end

  @doc """
  Checks a finite Port-client Core fragment against the supplied protocol profile.

  The target's first argument is the Port and its second is preparation input.
  Supply `calls: %{prepare: {Helpers, :prepare, 1}, reply: {Helpers, :await_reply, 1},
  decode: {Helpers, :decode, 1}}`. These helper contracts remain assumptions.
  The fragment requires `port_command/3` with `[:nosuspend]`, Boolean outcome
  cases, and reply patterns `{:data, payload}`, `:closed`, and `:timeout`.

  The caller bound adds `source_node_bound * source_node` to the protocol
  budget. The symbolic source-node charge covers supported local evaluation,
  bindings, argument retrieval, and finite case dispatch. Event charges cover
  contracted helper and primitive work. This is not concrete ERTS accounting.

  Only after Lean verifies the connection, semantics, and returned formula is
  `source_correspondence` set to `:checked`. The claim covers finite normally
  returning executions under the declared call, size and event-count contracts.
  Helper implementation correctness, exceptions, progress, and runtime charging
  remain unverified. Native receive and recursive clients are unsupported.
  Standard timeout, concurrency, Lean, and BEAM-binary options apply.

  ```elixir
  {:ok, result} = ReductionBounds.infer_port_bound({Client, :request, 2}, profile,
    calls: %{prepare: {Helpers, :prepare, 1}, reply: {Helpers, :await_reply, 1},
      decode: {Helpers, :decode, 1}})
  result.verification_scope.kind
  #=> :core_connected_port_client
  result.source_correspondence
  #=> :checked
  result.completion.theorem_status
  #=> :not_established
  ```
  """
  @spec infer_port_bound(target(), ReductionBounds.ProtocolCost.t(), [
          struct_inference_option() | {:calls, map()}
        ]) :: {:ok, map()} | {:error, term()}
  def infer_port_bound(target, profile, options \\ []) do
    with :ok <- validate_targets([target]),
         true <- Keyword.keyword?(options),
         {source_options, verify_options} = Keyword.split(options, [:calls]),
         {:ok, verify_options} <- validate_options(verify_options, :struct_bound),
         {:ok, candidate, proof} <-
           ReductionBounds.PortSourceProof.build(
             target,
             profile,
             source_options ++ Keyword.take(verify_options, [:beam_binaries])
           ),
         {:ok, result} <- verify_bound(target, candidate, proof, verify_options) do
      ReductionBounds.PortResult.verified(result, result.reports)
    else
      false -> {:error, :invalid_options}
      error -> error
    end
  end

  defp verify_bound(target, candidate, proof, options) do
    source = Map.get(candidate, :source, :translated)
    {proof, evidence} = ReductionBounds.ProofInput.audit_bound(proof, candidate)

    case verify_source(:inline, [target], [postlude: proof] ++ options, source) do
      {:ok, [{^target, {:ok, reports}}]} ->
        scope = ReductionBounds.ProofInput.scope_evidence(candidate)

        result =
          candidate |> Map.merge(evidence) |> Map.merge(scope) |> Map.put(:reports, reports)

        {:ok, result}

      {:ok, [{^target, {:error, reason}}]} ->
        {:error, reason}

      {:error, _reason} = error ->
        error
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

  defp proof_postludes(proof, :port_completion),
    do: ReductionBounds.ProofInput.port_completion_postludes(proof)

  defp proof_postludes(proof, :port_source),
    do: ReductionBounds.ProofInput.port_source_postludes(proof)

  defp proof_postludes(proof, :integer_bound_transfer),
    do: ReductionBounds.ProofInput.transfer_postludes(proof)

  defp proof_postludes(proof, :cost_contract_comparison),
    do: ReductionBounds.ProofInput.contract_postludes(proof)

  defp proof_postludes(proof, :integer_cost_fragment),
    do: ReductionBounds.ProofInput.integer_cost_postludes(proof)

  defp proof_postludes(proof, :integer_fragment),
    do: ReductionBounds.ProofInput.integer_postludes(proof)

  defp proof_postludes(proof, :struct_fragment), do: ReductionBounds.ProofInput.postludes(proof)

  defp proof_postludes(proof, :execution_fragment),
    do: ReductionBounds.ProofInput.execution_postludes(proof)

  defp proof_postludes(proof, _definition),
    do: ReductionBounds.ProofInput.generated_postludes(proof)

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

    allowed = option_defaults(source, defaults)

    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, allowed),
         nil <- Enum.find(options, fn option -> not valid_option_for?(source, option) end) do
      {:ok, options}
    else
      false -> {:error, :invalid_options}
      {:error, keys} -> invalid_option_keys(source, keys)
      {key, value} -> {:error, {:invalid_option, key, value}}
    end
  end

  defp invalid_option_keys(source, keys)
       when source in [:cost_comparison, :bound_transfer, :port_model],
       do: {:error, {:unknown_options, Enum.sort(keys)}}

  defp invalid_option_keys(_source, _keys), do: {:error, :invalid_options}

  defp option_defaults(:inline, defaults), do: [:postlude | defaults]
  defp option_defaults(:list_bound, defaults), do: [:input_contract | defaults]

  defp option_defaults(:port_model, defaults),
    do:
      [observations: %{}, completion: []] ++
        Keyword.drop(defaults, [:beam_binaries, :termination_suffixes])

  defp option_defaults(:struct_bound, defaults),
    do: Keyword.delete(defaults, :termination_suffixes)

  defp option_defaults(:integer_cost, defaults) do
    [
      input_sizes: nil,
      call_contracts: %{},
      recursive_invariant: nil,
      max_unfolding: 32,
      max_nodes: 10_000,
      cost_contract: nil
    ] ++
      Keyword.delete(defaults, :termination_suffixes)
  end

  defp option_defaults(:bound_transfer, defaults) do
    [input_sizes: nil, callee_correspondence: nil, max_unfolding: 32, max_nodes: 10_000] ++
      Keyword.delete(defaults, :termination_suffixes)
  end

  defp option_defaults(:cost_comparison, defaults),
    do: [budget: nil] ++ Keyword.drop(defaults, [:termination_suffixes, :beam_binaries])

  defp option_defaults(:integer_sizes, defaults),
    do: [input_sizes: nil] ++ Keyword.delete(defaults, :termination_suffixes)

  defp option_defaults(:execution_bound, defaults),
    do: [call_contracts: %{}] ++ Keyword.delete(defaults, :termination_suffixes)

  defp option_defaults(:periodic_bound, defaults),
    do: [:periodic_contract | Keyword.delete(defaults, :termination_suffixes)]

  defp option_defaults(_scope, defaults), do: defaults

  defp valid_option_for?(:port_model, {:observations, value}),
    do: is_map(value) and not is_struct(value)

  defp valid_option_for?(:port_model, {:completion, value}), do: Keyword.keyword?(value)

  defp valid_option_for?(:bound_transfer, {:callee_correspondence, %Lynx.Lean{source: source}}),
    do: is_binary(source)

  defp valid_option_for?(:bound_transfer, {:callee_correspondence, value}),
    do: value in [nil, :shared]

  defp valid_option_for?(:bound_transfer, {name, value})
       when name in [:max_unfolding, :max_nodes],
       do: valid_option_for?(:integer_cost, {name, value})

  defp valid_option_for?(:cost_comparison, {:budget, _value}), do: true

  defp valid_option_for?(:integer_cost, {:cost_contract, nil}), do: true

  defp valid_option_for?(:integer_cost, {:cost_contract, value}),
    do: is_struct(value, ReductionBounds.CostContract)

  defp valid_option_for?(:integer_cost, {:call_contracts, value}), do: is_map(value)
  defp valid_option_for?(:integer_cost, {:recursive_invariant, nil}), do: true

  defp valid_option_for?(:integer_cost, {:recursive_invariant, values}) do
    is_list(values) and Enum.all?(values, &ReductionBounds.IntegerSize.valid?/1)
  end

  defp valid_option_for?(:integer_cost, {:max_unfolding, value}),
    do: is_integer(value) and value in 0..1024

  defp valid_option_for?(:integer_cost, {:max_nodes, value}),
    do: is_integer(value) and value in 1..1_000_000

  defp valid_option_for?(_scope, option), do: valid_option?(option)

  defp valid_option?({:input_sizes, nil}), do: true

  defp valid_option?({:input_sizes, values}) do
    is_list(values) and Enum.all?(values, &ReductionBounds.IntegerSize.valid?/1)
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
    {lean_options, task_options} = Keyword.pop!(options, :lean_options)
    {:ok, supervisor} = Task.Supervisor.start_link()

    try do
      supervisor
      |> Task.Supervisor.async_stream_nolink(
        targets,
        fn target ->
          {target, verify_target(target, translation, lean_options, definition)}
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

  defp verify_target(target, translation, lean_options, definition) do
    reports =
      ReductionBounds.Verification.verify!(translation,
        target: target,
        definition: definition,
        options: lean_options
      )

    if reports != [] and Enum.all?(reports, &(&1.status == :ok)) do
      {:ok, reports}
    else
      {:error, {:verification_failed, reports}}
    end
  rescue
    error -> {:error, {:lynx, error}}
  end
end
