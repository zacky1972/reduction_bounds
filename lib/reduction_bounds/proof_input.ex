defmodule ReductionBounds.ProofInput do
  @moduledoc false

  alias ReductionBounds.{CoreFragment, Normalize}

  @sources ["CoreFragment.lean", "StructRules.lean", "Normalize.lean"]
  @insertion_theorems ~w(
    Reverse.listValueAndBound
    enumReverseListValue
    enumReverseCostBound
    bufferRotationSize
    insertCostBound
    insertContents
  )

  @type read_error :: {:read_lean, Path.t(), File.posix()}
  @typep translation :: %Lynx.Translation{}

  @spec assemble(translation()) :: [map()]
  def assemble(translation) do
    translation
    |> Lynx.Translation.assemble(cache: false)
    |> Enum.map(fn
      %{"module" => "Erlang.postlude"} = file ->
        Map.update!(file, "imports", &Enum.uniq(["Erlang.erlang", "Erlang.maps" | &1]))

      file ->
        file
    end)
  end

  @spec postludes(Lynx.Lean.t()) ::
          {:ok, [Lynx.Lean.t()]} | {:error, read_error() | {:priv_dir, :bad_name}}
  def postludes(%Lynx.Lean{} = proof), do: packaged_postludes(proof, @sources)

  @spec execution_postludes(Lynx.Lean.t()) ::
          {:ok, [Lynx.Lean.t()]} | {:error, read_error() | {:priv_dir, :bad_name}}
  def execution_postludes(%Lynx.Lean{} = proof) do
    packaged_postludes(proof, @sources ++ ["ExecutionBound.lean"])
  end

  @spec integer_postludes(Lynx.Lean.t()) ::
          {:ok, [Lynx.Lean.t()]} | {:error, read_error() | {:priv_dir, :bad_name}}
  def integer_postludes(%Lynx.Lean{} = proof) do
    packaged_postludes(proof, ["IntegerSize.lean", "IntegerAnalysis.lean"])
  end

  @spec integer_cost_postludes(Lynx.Lean.t()) ::
          {:ok, [Lynx.Lean.t()]} | {:error, read_error() | {:priv_dir, :bad_name}}
  def integer_cost_postludes(%Lynx.Lean{} = proof) do
    packaged_postludes(proof, [
      "IntegerSize.lean",
      "IntegerAnalysis.lean",
      "IntegerCost.lean",
      "IntegerCostSource.lean"
    ])
  end

  @spec contract_postludes(Lynx.Lean.t()) ::
          {:ok, [Lynx.Lean.t()]} | {:error, read_error() | {:priv_dir, :bad_name}}
  def contract_postludes(%Lynx.Lean{} = proof) do
    packaged_postludes(proof, [
      "IntegerSize.lean",
      "IntegerAnalysis.lean",
      "IntegerCost.lean",
      "CostContract.lean",
      "BoundTransfer.lean"
    ])
  end

  @spec transfer_postludes(Lynx.Lean.t()) ::
          {:ok, [Lynx.Lean.t()]} | {:error, read_error() | {:priv_dir, :bad_name}}
  def transfer_postludes(%Lynx.Lean{} = proof) do
    packaged_postludes(proof, [
      "IntegerSize.lean",
      "IntegerAnalysis.lean",
      "IntegerCost.lean",
      "IntegerCostSource.lean",
      "CostContract.lean",
      "BoundTransfer.lean"
    ])
  end

  defp packaged_postludes(proof, sources) do
    case :code.priv_dir(:reduction_bounds) do
      {:error, reason} -> {:error, {:priv_dir, reason}}
      directory -> load_sources(proof, List.to_string(directory), sources)
    end
  end

  @spec postludes(Lynx.Lean.t(), Path.t()) ::
          {:ok, [Lynx.Lean.t()]} | {:error, read_error()}
  def postludes(%Lynx.Lean{} = proof, priv_dir), do: load_sources(proof, priv_dir, @sources)

  defp load_sources(proof, priv_dir, sources) do
    lean_dir = Path.join([priv_dir, "lean", "reduction_bounds"])

    case Enum.reduce_while(sources, [], &load_source(&1, &2, lean_dir)) do
      {:error, _reason} = error -> error
      sources -> {:ok, Enum.reverse(sources, [proof])}
    end
  end

  defp load_source(filename, sources, lean_dir) do
    path = Path.join(lean_dir, filename)
    {:cont, [Lynx.Lean.from_file!(path) | sources]}
  rescue
    error in File.Error -> {:halt, {:error, {:read_lean, error.path, error.reason}}}
  end

  @spec audit_bound(Lynx.Lean.t(), map()) :: {Lynx.Lean.t(), map()}
  def audit_bound(%Lynx.Lean{} = proof, candidate) do
    case case_study_theorems(candidate) do
      [] ->
        {proof, %{}}

      theorems ->
        names = Enum.map_join(theorems, ", ", &"``#{&1}")

        audit = """

        open Lean in
        run_cmd do
          for theoremName in #[#{names}] do
            for dependency in ← Lean.collectAxioms theoremName do
              unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
                throwError m!"Unexpected axiom in {theoremName}: {dependency}"
        """

        {%{proof | source: proof.source <> audit}, %{checked_theorems: theorems}}
    end
  end

  @spec scope_evidence(map()) :: map()
  def scope_evidence(%{source: :cost_contract_comparison} = candidate) do
    %{
      verification_scope: %{
        kind: candidate.proof_scope,
        contracts: %{smaller: candidate.smaller.id, larger: candidate.larger.id},
        checked: [
          :size_monotonicity,
          :operation_order,
          :budget_order,
          :conditional_execution_order
        ],
        assumptions: %{execution_conditions: candidate.execution_conditions},
        trusted: [:metadata_validation, :expression_serialization],
        unverified: [
          :target_applicability,
          :bound_transfer,
          :runtime_correspondence,
          :wall_clock_time
        ]
      }
    }
  end

  def scope_evidence(%{source: :integer_bound_transfer} = candidate) do
    %{
      verification_scope: %{
        kind: candidate.proof_scope,
        contracts: %{from: candidate.source_contract.id, to: candidate.destination_contract.id},
        checked: [
          :source_bound_replay,
          :operation_order,
          :input_coverage,
          :core_value_agreement,
          :bound_transfer,
          :termination_under_source_call_contracts
        ],
        assumptions: %{
          input_sizes: candidate.input_sizes,
          recursive_invariant: candidate.original_bound.conditions.recursive_invariant,
          source_call_contracts: candidate.original_bound.conditions.calls,
          callee_models: candidate.conditions.callee_models
        },
        trusted: [
          :debug_information_extraction,
          :core_reification,
          :expression_serialization,
          :metadata_validation
        ],
        unverified: [:runtime_correspondence, :wall_clock_time]
      }
    }
  end

  def scope_evidence(_candidate), do: %{}

  defp case_study_theorems(%{source: :integer_cost_fragment} = candidate) do
    global =
      ~w(ReductionBounds.IntegerCost.inclusionSound ReductionBounds.IntegerCost.derivationSound
      ReductionBounds.IntegerCost.derivationTerminates ReductionBounds.IntegerCost.derivationInvariant
      ReductionBounds.IntegerCostSource.sourceAgreement ReductionBounds.IntegerCostSource.sourceComplete)

    global ++ integer_cost_theorems(candidate, "")
  end

  defp case_study_theorems(%{source: :cost_contract_comparison} = candidate) do
    theorems =
      ~w(ReductionBounds.CostContract.Expr.monotone ReductionBounds.CostContract.ExprLe.sound
      ReductionBounds.CostContract.functionsMonotone ReductionBounds.CostContract.FunctionsLe.sound
      ReductionBounds.CostContract.budgetMonotone smallerMonotone largerMonotone
      functionCertificate operationOrdering allBudgetOrdering
      ReductionBounds.BoundTransfer.compareExecution ReductionBounds.BoundTransfer.runsDeterministic
      ReductionBounds.BoundTransfer.executionCostLe ReductionBounds.BoundTransfer.derivationCallsWithin
      ReductionBounds.BoundTransfer.compareUnderContracts
      executionCostOrdering executionOrderingUnderContracts)

    if is_nil(candidate.budget),
      do: theorems,
      else: theorems ++ ~w(suppliedBudgetValues suppliedBudgetOrdering)
  end

  defp case_study_theorems(%{source: :integer_bound_transfer} = candidate) do
    generic =
      ~w(ReductionBounds.IntegerCost.derivationSound ReductionBounds.IntegerCost.derivationTerminates
      ReductionBounds.IntegerCostSource.sourceAgreement ReductionBounds.IntegerCostSource.sourceComplete
      ReductionBounds.BoundTransfer.compareFromLarger ReductionBounds.BoundTransfer.transferDerivedBound
      ReductionBounds.BoundTransfer.transferBudget ReductionBounds.BoundTransfer.transferTerminates)

    {globals, local} =
      candidate.comparison
      |> case_study_theorems()
      |> Enum.split_with(&String.starts_with?(&1, "ReductionBounds."))

    comparison = Enum.map(local, &("Comparison." <> &1))

    generic ++
      globals ++
      comparison ++
      integer_cost_theorems(candidate.original_bound, "SourceBound.") ++
      ~w(transferInputCoverage transferBudgetIdentity transferCallees sourceContractBound
      transferredCostChain transferredExecutionBound transferredNumericBound transferredSourceBound transferredTotal)
  end

  defp case_study_theorems(%{source: :integer_fragment}),
    do:
      ~w(ReductionBounds.IntegerAnalysis.inferSound targetIntegerSizeCorrect targetIntegerTraceCorrect targetIntegerSizeBound)

  defp case_study_theorems(%{source: :lynx_builtin, value_model: :membership}),
    do: ~w(listRulesSound listPathBounds searchCostDerivation listValueAndBound)

  defp case_study_theorems(%{source: :lynx_builtin, value_model: :reversal}),
    do: ~w(listRulesSound reverseCostDerivation reverseResult listValueAndBound)

  defp case_study_theorems(%{source: :composed}),
    do: ~w(Member.listValueAndBound Reverse.listValueAndBound programValueAndBound)

  defp case_study_theorems(%{value_model: :circular_buffer_model}), do: @insertion_theorems

  defp case_study_theorems(%{value_model: :circular_buffer_sequence_model}) do
    @insertion_theorems ++
      ~w(
        bufferObligations
        ReductionBounds.Periodic.eventCount
        ReductionBounds.Periodic.costBound
        insertManyRotationCountFrom
        insertManyCostBoundFrom
        insertManyRotationCount
        insertManyCostBound
        insertManyLatest
      )
  end

  defp case_study_theorems(_candidate), do: []

  defp integer_cost_theorems(candidate, prefix) do
    local =
      ~w(costUniqueNames costTranslation costDerivation costCandidate integerCostValueAgreement
      integerCostSound integerCostInvariant integerCostSourceBound integerCostTotal)

    invariant = if candidate.conditions.recursive_invariant, do: ["costInvariants"], else: []
    own = Enum.map(local ++ invariant, &(prefix <> &1))

    reused =
      Enum.flat_map(candidate.call_contracts, fn
        {key, %{origin: :checked_model_bound, checked_bound: checked}} ->
          [
            prefix <> "costReuse#{key}"
            | integer_cost_theorems(checked, prefix <> "Callee#{key}.")
          ]

        _ ->
          []
      end)

    own ++ reused
  end

  @spec certificate_source([Normalize.certificate()]) :: String.t()
  def certificate_source(certificates) do
    declarations =
      certificates
      |> Enum.with_index()
      |> Enum.map_join("\n", fn {certificate, index} -> declaration(certificate, index) end)

    "namespace ReductionBounds.Core\n" <> declarations <> "\nend ReductionBounds.Core\n"
  end

  @spec normalization_source(String.t(), CoreFragment.expr(), CoreFragment.expr()) :: String.t()
  def normalization_source(source, original, normalized) do
    """
    namespace ReductionBounds.Core

    def extractedCore : SourceExpr := #{source}
    def decodedCore : Expr := #{expression(original)}
    def normalizedCore : Expr := #{expression(normalized)}

    theorem coreDecoding : extractedCore.lower = decodedCore := by decide

    theorem coreNormalization : CheckedRewrite [] decodedCore normalizedCore := by
      unfold decodedCore normalizedCore
      repeat' first
        | apply CheckedRewrite.same
        | apply CheckedRewrite.readField
        | apply CheckedRewrite.caseMap
        | apply CheckedRewrite.letAlias
        | decide

    theorem coreValueAgreement (external : OpaqueEval) (env : Env) :
        extractedCore.run external env = eval external env normalizedCore :=
      sourceNormalizationSound extractedCore decodedCore normalizedCore
        (by decide) coreDecoding coreNormalization external env

    end ReductionBounds.Core
    """
  end

  defp declaration(certificate, index) do
    %{facts: facts, original: original, normalized: normalized, rewrite: rewrite} = certificate

    """
    def certificate#{index} : Certificate := {
      facts := [#{Enum.map_join(facts, ", ", &fact/1)}]
      original := #{expression(original)}
      normalized := #{expression(normalized)}
      rewrite := #{rewrite(rewrite)}
    }

    theorem accepted#{index} : certificate#{index}.check = true := by
      decide

    theorem agreement#{index} (external : OpaqueEval) (env : Env)
        (holds : FactsHold env certificate#{index}.facts) :
        eval external env certificate#{index}.original =
          eval external env certificate#{index}.normalized :=
      certificate#{index}.sound external env accepted#{index} holds
    """
  end

  defp fact({subject, key}), do: "⟨#{string(subject)}, #{string(key)}⟩"

  defp rewrite({:read_field, subject, key, binder, fallback}) do
    ".readField #{string(subject)} #{string(key)} #{string(binder)} #{expression(fallback)}"
  end

  @spec expression(CoreFragment.expr()) :: String.t()
  def expression({:var, name}), do: node("var", [string(name)])
  def expression({:int, value}), do: node("int", ["(#{value})"])
  def expression({:atom, value}), do: node("atom", [string(value)])
  def expression({:opaque, id}), do: node("opaque", [string(id)])

  def expression({:let_in, name, rhs, body}),
    do: node("letIn", [string(name), expression(rhs), expression(body)])

  def expression({:case_map, subject, pattern, matched, fallback}) do
    node("caseMap", [
      expression(subject),
      pattern(pattern),
      expression(matched),
      expression(fallback)
    ])
  end

  def expression({:case_map_guarded, subject, pattern, condition, matched, fallback}) do
    node("caseMapGuarded", [
      expression(subject),
      pattern(pattern),
      expression(condition),
      expression(matched),
      expression(fallback)
    ])
  end

  def expression({:guarded, condition, success, failure}),
    do: node("guarded", Enum.map([condition, success, failure], &expression/1))

  def expression({:field, subject, key}), do: node("field", [expression(subject), string(key)])

  def expression({:update, subject, key, rhs}),
    do: node("update", [expression(subject), string(key), expression(rhs)])

  def expression({:is_integer, operand}), do: node("isInteger", [expression(operand)])
  def expression({:is_map, operand}), do: node("isMap", [expression(operand)])

  def expression({op, left, right}) when op in [:ge, :sub],
    do: node(Atom.to_string(op), [expression(left), expression(right)])

  defp pattern(%{tag: tag, fields: fields}) do
    tag = if tag, do: "some #{string(tag)}", else: "none"

    fields =
      Enum.map_join(fields, ", ", fn {key, binder} -> "(#{string(key)}, #{string(binder)})" end)

    "⟨#{tag}, [#{fields}]⟩"
  end

  defp node(constructor, arguments), do: "(.#{constructor} #{Enum.join(arguments, " ")})"

  @spec string(String.t()) :: String.t()
  def string(value) do
    if String.match?(value, ~r/^[ -~]*\z/) do
      escaped = value |> String.replace("\\", "\\\\") |> String.replace("\"", "\\\"")
      "\"#{escaped}\""
    else
      chars = Enum.map_join(String.to_charlist(value), ", ", &"Char.ofNat #{&1}")
      "(String.ofList [#{chars}])"
    end
  end
end
