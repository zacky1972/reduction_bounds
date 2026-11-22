defmodule ReductionBounds.BoundTransfer do
  @moduledoc false

  alias ReductionBounds.{
    ContractComparison,
    IntegerAnalysis,
    IntegerCostBound,
    IntegerCostSource,
    IntegerSize
  }

  @evidence_fields [
    :target,
    :source,
    :input_sizes,
    :result_size,
    :upper_bound,
    :expression,
    :core_source,
    :translation_certificate,
    :derivation,
    :call_contracts,
    :conditions,
    :cost_contract
  ]

  @spec infer(map(), term(), keyword()) :: {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer(original, destination, options) do
    with {:ok, source} <- refresh(original, options, []),
         {:ok, comparison, _proof} <-
           ContractComparison.infer(destination, source.cost_contract, source.upper_bound),
         {:ok, inputs} <- input_sizes(source.input_sizes, options[:input_sizes]),
         {:ok, relation} <-
           callee_relation(source.call_contracts, options[:callee_correspondence]) do
      candidate = %{
        source: :integer_bound_transfer,
        target: source.target,
        original_bound: source,
        comparison: comparison,
        source_contract: source.cost_contract,
        destination_contract: destination,
        input_sizes: inputs,
        result_size: source.result_size,
        upper_bound: source.upper_bound,
        upper_bound_contract: source.cost_contract.id,
        upper_bound_value: comparison.budget_values.larger,
        callee_relation: relation,
        conditions: %{
          source: source.conditions,
          input_sizes: inputs,
          input_coverage: :checked,
          source_call_contracts: :assumed,
          callee_models: relation_kind(relation)
        },
        proof_scope: :reified_core_integer_bound_transfer,
        bound_transfer: :checked,
        source_bound_rechecked: true,
        comparison_rechecked: true,
        contract_instantiation: :checked,
        callee_correspondence: relation_status(relation),
        termination: :finite_derivation_under_source_call_contracts,
        unresolved_obligations: [:runtime_correspondence],
        runtime_correspondence: :not_checked
      }

      {:ok, candidate, proof(candidate)}
    end
  end

  defp refresh(original, options, seen) do
    with :ok <- validate_original(original),
         :ok <- acyclic(original.target, seen),
         {:ok, calls} <-
           replay_calls(original.call_contracts, options, [original.target | seen]),
         {:ok, fresh, _proof} <-
           IntegerCostBound.infer(original.target, replay_options(original, calls, options)) do
      match_evidence(original, fresh)
    end
  end

  defp validate_original(
         %{
           source: :integer_cost_fragment,
           target: {module, function, arity},
           input_sizes: inputs,
           conditions: conditions,
           call_contracts: calls
         } = bound
       )
       when is_atom(module) and is_atom(function) and is_integer(arity) and arity >= 0 and
              is_list(inputs) and is_map(conditions) and is_map(calls) do
    case Enum.find(@evidence_fields, &(not Map.has_key?(bound, &1))) do
      nil -> :ok
      field -> {:error, {:invalid_original_bound, field}}
    end
  end

  defp validate_original(_bound), do: {:error, :invalid_original_bound}

  defp acyclic(target, seen) do
    if target in seen,
      do: {:error, {:cyclic_bound_reuse, target}},
      else: :ok
  end

  defp replay_calls(calls, options, seen) do
    Enum.reduce_while(calls, {:ok, %{}}, fn {_key, call}, {:ok, result} ->
      case replay_call(call, options, seen) do
        {:ok, target, value} -> {:cont, {:ok, Map.put(result, target, value)}}
        {:error, _reason} = error -> {:halt, error}
      end
    end)
  end

  defp replay_call(%{target: target, checked_bound: bound}, options, seen) do
    with {:ok, fresh} <- refresh(bound, options, seen),
         true <- fresh.target == target do
      {:ok, target, bound}
    else
      false -> {:error, {:callee_target_mismatch, target}}
      {:error, _reason} = error -> error
    end
  end

  defp replay_call(
         %{target: target, input_size: input, result_size: output, upper_bound: bound},
         _options,
         _seen
       ),
       do: {:ok, target, %{input_size: input, result_size: output, upper_bound: bound}}

  defp replay_call(value, _options, _seen), do: {:error, {:invalid_original_call_contract, value}}

  defp replay_options(original, calls, options) do
    Keyword.merge(Keyword.take(options, [:beam_binaries, :max_unfolding, :max_nodes]),
      input_sizes: original.input_sizes,
      call_contracts: calls,
      recursive_invariant: original.conditions[:recursive_invariant],
      cost_contract: original.cost_contract
    )
  end

  defp match_evidence(original, fresh) do
    case Enum.find(@evidence_fields, &(Map.fetch!(original, &1) != Map.fetch!(fresh, &1))) do
      nil -> {:ok, fresh}
      field -> {:error, {:original_bound_mismatch, original.target, field}}
    end
  end

  defp input_sizes(source, nil), do: {:ok, source}

  defp input_sizes(source, inputs) when is_list(inputs) and length(inputs) == length(source) do
    pairs = Enum.zip(inputs, source)

    if Enum.all?(pairs, fn {actual, required} -> IntegerCostBound.included?(actual, required) end),
       do: {:ok, Enum.map(inputs, &IntegerSize.normalize/1)},
       else: {:error, {:insufficient_transfer_inputs, inputs, source}}
  end

  defp input_sizes(source, inputs), do: {:error, {:invalid_transfer_inputs, inputs, source}}

  defp callee_relation(calls, nil) when map_size(calls) == 0, do: {:ok, :shared}
  defp callee_relation(_calls, :shared), do: {:ok, :shared}
  defp callee_relation(_calls, %Lynx.Lean{} = proof), do: {:ok, proof}

  defp callee_relation(calls, nil),
    do:
      {:error, {:unresolved_callee_correspondence, Enum.map(calls, fn {_key, c} -> c.target end)}}

  defp relation_kind(:shared), do: :shared_external_model
  defp relation_kind(%Lynx.Lean{}), do: :proved_external_agreement
  defp relation_status(:shared), do: :shared_model
  defp relation_status(%Lynx.Lean{}), do: :checked

  @spec proof(map()) :: Lynx.Lean.t()
  def proof(candidate) do
    source = IntegerCostBound.proof(candidate.original_bound, candidate.comparison.operations)
    comparison = ContractComparison.proof(candidate.comparison)

    %Lynx.Lean{
      file: "generated_integer_bound_transfer.lean",
      span: {1, 1},
      indentation: 0,
      source:
        "namespace SourceBound\n" <>
          source.source <>
          "\nend SourceBound\n" <>
          "namespace Comparison\n" <>
          comparison.source <>
          "\nend Comparison\n" <>
          inputs_proof(candidate) <>
          relation_proof(candidate.callee_relation) <>
          transfer_proof(candidate)
    }
  end

  defp inputs_proof(candidate) do
    coverage = candidate |> coverage() |> String.replace("\n", "\n  ")

    """
    open ReductionBounds.IntegerSize
    def transferInputs : ReductionBounds.IntegerAnalysis.State := #{state(candidate.input_sizes)}
    theorem transferInputCoverage (env : ReductionBounds.IntegerAnalysis.Env)
        (pre : ReductionBounds.IntegerAnalysis.Covers transferInputs env) :
        ReductionBounds.IntegerAnalysis.Covers SourceBound.costInputs env := by
      #{coverage}
    theorem transferBudgetIdentity : SourceBound.costSummary.budget = Comparison.suppliedBudget := by decide
    """
  end

  defp coverage(candidate) do
    if :unreachable in candidate.input_sizes,
      do: "exact False.elim pre",
      else: reachable_coverage(candidate)
  end

  defp reachable_coverage(candidate) do
    branches =
      candidate.input_sizes
      |> Enum.zip(candidate.original_bound.input_sizes)
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {{actual, required}, index} ->
        "· exact ReductionBounds.IntegerCost.inclusionSound #{IntegerAnalysis.size(actual)} " <>
          "#{IntegerAnalysis.size(required)} (by decide) (env #{index}) (pre #{index})"
      end)

    rest = Enum.reduce(candidate.input_sizes, "rest", fn _, acc -> "(Nat.succ #{acc})" end)

    "change ∀ index, _ at pre\nchange ∀ index, _\n" <>
      "intro index\nrcases index with #{natural_cases(length(candidate.input_sizes))}\n" <>
      branches <> "\n· exact pre #{rest}"
  end

  defp natural_cases(0), do: "rest"
  defp natural_cases(count), do: "_ | (#{natural_cases(count - 1)})"

  defp state(inputs) do
    if :unreachable in inputs do
      "none"
    else
      clauses =
        inputs
        |> Enum.with_index()
        |> Enum.map_join("\n", fn {size, index} ->
          "| #{index} => #{IntegerAnalysis.size(size)}"
        end)

      "some (fun index => match index with\n#{clauses}\n| _ => .bounded {})"
    end
  end

  defp relation_proof(:shared) do
    """
    theorem transferCallees (external : ReductionBounds.IntegerCost.External) :
        ReductionBounds.BoundTransfer.ExternalAgreement
          (fun key argument => (SourceBound.costContracts key).input.Holds argument) external external := by
      constructor
      · intro key argument _held; rfl
      · intro key argument _held; exact Nat.le_refl _
    """
  end

  defp relation_proof(%Lynx.Lean{} = proof) do
    proof.source <>
      """

      theorem transferCallees : ReductionBounds.BoundTransfer.ExternalAgreement
          (fun key argument => (SourceBound.costContracts key).input.Holds argument)
          transferExternalA transferExternalB := transferCalleeAgreement
      """
  end

  defp external(:shared),
    do:
      {"(external : ReductionBounds.IntegerCost.External)", "external", "external",
       "transferCallees external"}

  defp external(%Lynx.Lean{}),
    do: {"", "transferExternalA", "transferExternalB", "transferCallees"}

  defp transfer_proof(candidate) do
    {parameters, a, b, agreement} = external(candidate.callee_relation)
    {_, function, _} = candidate.target
    name = IntegerCostSource.string(Atom.to_string(function))
    bound = candidate.upper_bound_value

    """
    theorem sourceContractBound #{parameters}
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts #{b})
        (env : ReductionBounds.IntegerAnalysis.Env)
        (pre : ReductionBounds.IntegerAnalysis.Covers transferInputs env)
        (value : Int) (cost : Nat)
        (run : ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.largerCharges #{b}
          SourceBound.costProgram env value cost) :
        SourceBound.costSummary.size.Holds value ∧ cost ≤ SourceBound.costSummary.budget.eval Comparison.largerCharges :=
      SourceBound.integerCostSound Comparison.largerCharges #{b} Comparison.largerMonotone
        calls env (transferInputCoverage env pre) value cost run

    theorem transferredCostChain #{parameters}
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts #{b})
        (env : ReductionBounds.IntegerAnalysis.Env)
        (pre : ReductionBounds.IntegerAnalysis.Covers transferInputs env)
        (value : Int) (cost : Nat)
        (run : ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges #{a}
          SourceBound.costProgram env value cost) :
        ∃ sourceValue sourceCost,
          ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.largerCharges #{b}
            SourceBound.costProgram env sourceValue sourceCost ∧
          value = sourceValue ∧ SourceBound.costSummary.size.Holds value ∧ cost ≤ sourceCost ∧
          sourceCost ≤ Comparison.suppliedBudget.eval Comparison.largerCharges := by
      have chain := ReductionBounds.BoundTransfer.transferDerivedBound Comparison.operationOrdering
        Comparison.largerMonotone calls (#{agreement}) SourceBound.costDerivation
        (transferInputCoverage env pre) run
      simpa only [transferBudgetIdentity] using chain

    theorem transferredExecutionBound #{parameters}
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts #{b})
        (env : ReductionBounds.IntegerAnalysis.Env)
        (pre : ReductionBounds.IntegerAnalysis.Covers transferInputs env)
        (value : Int) (cost : Nat)
        (run : ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges #{a}
          SourceBound.costProgram env value cost) :
        SourceBound.costSummary.size.Holds value ∧ cost ≤ Comparison.suppliedBudget.eval Comparison.largerCharges := by
      have bound := ReductionBounds.BoundTransfer.transferBudget Comparison.operationOrdering
        Comparison.largerMonotone calls (#{agreement}) SourceBound.costDerivation
        (transferInputCoverage env pre) run
      simpa only [transferBudgetIdentity] using bound

    theorem transferredNumericBound #{parameters}
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts #{b})
        (env : ReductionBounds.IntegerAnalysis.Env)
        (pre : ReductionBounds.IntegerAnalysis.Covers transferInputs env)
        (value : Int) (cost : Nat)
        (run : ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges #{a}
          SourceBound.costProgram env value cost) : cost ≤ #{bound} := by
      have result := transferredExecutionBound #{if parameters == "", do: "", else: "external"} calls env pre value cost run
      rw [Comparison.suppliedBudgetValues.2] at result
      exact result.2

    theorem transferredSourceBound #{parameters}
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts #{b})
        (env : ReductionBounds.IntegerAnalysis.Env)
        (pre : ReductionBounds.IntegerAnalysis.Covers transferInputs env) (value : Int)
        (run : ReductionBounds.IntegerCostSource.Evaluates SourceBound.costSource #{name}
          SourceBound.costNames #{a} SourceBound.costSource env value) :
        ∃ cost, ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges #{a}
          SourceBound.costProgram env value cost ∧ SourceBound.costSummary.size.Holds value ∧ cost ≤ #{bound} := by
      obtain ⟨cost, execution⟩ :=
        (SourceBound.integerCostValueAgreement Comparison.smallerCharges #{a} env value).mp run
      exact ⟨cost, execution,
        (transferredExecutionBound #{if parameters == "", do: "", else: "external"} calls env pre value cost execution).1,
        transferredNumericBound #{if parameters == "", do: "", else: "external"} calls env pre value cost execution⟩

    theorem transferredTotal #{parameters}
        (calls : ReductionBounds.IntegerCost.ContractsHold Comparison.largerCharges SourceBound.costContracts #{b})
        (env : ReductionBounds.IntegerAnalysis.Env)
        (pre : ReductionBounds.IntegerAnalysis.Covers transferInputs env) :
        ∃ value cost, ReductionBounds.IntegerCost.Runs SourceBound.costProgram Comparison.smallerCharges #{a}
          SourceBound.costProgram env value cost ∧
          ReductionBounds.IntegerCostSource.Evaluates SourceBound.costSource #{name} SourceBound.costNames #{a}
            SourceBound.costSource env value ∧ SourceBound.costSummary.size.Holds value ∧ cost ≤ #{bound} := by
      obtain ⟨value, cost, run, result, _bound⟩ :=
        ReductionBounds.BoundTransfer.transferTerminates Comparison.operationOrdering Comparison.largerMonotone
          calls (#{agreement}) SourceBound.costDerivation (transferInputCoverage env pre)
      exact ⟨value, cost, run,
        (SourceBound.integerCostValueAgreement Comparison.smallerCharges #{a} env value).mpr ⟨cost, run⟩,
        result, transferredNumericBound #{if parameters == "", do: "", else: "external"} calls env pre value cost run⟩
    """
  end
end
