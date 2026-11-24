defmodule ReductionBounds.PeriodicBound do
  @moduledoc false

  alias ReductionBounds.SearchBound

  @type formula ::
          non_neg_integer()
          | atom()
          | {:measure, :periodic_measure}
          | {:add | :sub | :mul | :div, formula(), formula()}

  @spec event_count(formula(), formula(), formula(), formula(), formula()) :: formula()
  def event_count(period, stride, origin, initial, steps) do
    {:div, subtract(add(initial, multiply(steps, stride)), origin), period}
  end

  @spec cost_bound(term(), term(), term(), term()) ::
          {:add, {:mul, term(), term()}, {:mul, term(), term()}}
  def cost_bound(base, surcharge, events, steps) do
    {:add, {:mul, steps, base}, {:mul, events, surcharge}}
  end

  @spec infer(ReductionBounds.target(), [binary()], Lynx.Lean.t() | nil) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer({_, _, 2} = target, beams, contract) do
    with {:ok, core} <- SearchBound.core_function(target, beams),
         {:ok, stride} <- counter_stride(core, target) do
      candidate = candidate(target, stride, contract)
      {:ok, candidate, proof(candidate, contract)}
    end
  end

  def infer(target, _beams, _contract), do: {:error, {:unsupported_target, target}}

  defp counter_stride(core, target) do
    case counter(:cerl_trees.map(&:cerl.set_ann(&1, []), core)) do
      {:ok, stride} -> {:ok, stride}
      :unsupported -> {:error, {:unsupported_periodic_transition, target}}
    end
  end

  defp counter(
         {:c_fun, [], [{:c_var, [], state}, {:c_var, [], period}],
          {:c_let, [], [{:c_var, [], advanced}],
           {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :+},
            [{:c_var, [], state}, {:c_literal, [], stride}]},
           {:c_case, [],
            {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :>=},
             [{:c_var, [], advanced}, {:c_var, [], period}]}, clauses}}}
       )
       when is_integer(stride) and stride > 0 and advanced != period and state != period do
    case Enum.sort_by(clauses, &branch_label/1) do
      [ordinary, event] ->
        if ordinary?(ordinary, advanced) and event?(event, advanced, period),
          do: {:ok, stride},
          else: :unsupported

      _ ->
        :unsupported
    end
  end

  defp counter(_core), do: :unsupported

  defp branch_label({:c_clause, [], [{:c_literal, [], flag}], {:c_literal, [], true}, _body}),
    do: flag

  defp branch_label(_clause), do: nil

  defp ordinary?(
         {:c_clause, [], [{:c_literal, [], false}], {:c_literal, [], true},
          {:c_tuple, [], [{:c_var, [], advanced}, {:c_literal, [], false}]}},
         advanced
       ),
       do: true

  defp ordinary?(_clause, _advanced), do: false

  defp event?(
         {:c_clause, [], [{:c_literal, [], true}], {:c_literal, [], true},
          {:c_let, [], [{:c_var, [], remainder}],
           {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :-},
            [{:c_var, [], advanced}, {:c_var, [], period}]},
           {:c_tuple, [], [{:c_var, [], remainder}, {:c_literal, [], true}]}}},
         advanced,
         period
       ),
       do: true

  defp event?(_clause, _advanced, _period), do: false

  defp candidate(target, stride, contract) do
    events = event_count(:period, stride, 0, :initial, :n)

    result = %{
      target: target,
      source: :periodic_fragment,
      metric: :symbolic_cost,
      periodic_rule: :constant_stride_reset,
      period: :period,
      stride: stride,
      origin: 0,
      size_measure: :pending_count,
      event_count: events,
      upper_bound: cost_bound(:base, :surcharge, events, :n),
      conditions: %{
        derived: [
          {:domain, :natural_state_and_period},
          {:invariant, {:lt, :state, :period}},
          {:stride_fits, {:le, stride, :period}},
          {:reset, :subtract_period},
          {:size_measure, :pending_count}
        ],
        supplied: supplied_conditions(contract)
      }
    }

    add_measured_bound(result, contract)
  end

  defp supplied_conditions(nil), do: []

  defp supplied_conditions(%Lynx.Lean{source: source}) do
    [
      {:invariant, :periodic_invariant},
      {:size_measure, :periodic_measure},
      {:lean_source, source}
    ]
  end

  defp add_measured_bound(result, nil), do: result

  defp add_measured_bound(result, _contract) do
    events = event_count(:period, result.stride, 0, {:measure, :periodic_measure}, :n)

    Map.merge(result, %{
      measured_event_upper_bound: events,
      measured_upper_bound: cost_bound(:base, :surcharge, events, :n)
    })
  end

  defp proof(candidate, contract) do
    %Lynx.Lean{
      file: "generated_periodic_bound.lean",
      span: {1, 1},
      indentation: 0,
      source: target_source(candidate) <> contract_source(candidate, contract)
    }
  end

  defp target_source(candidate) do
    """
    namespace ReductionBounds.Periodic

    def inferredStride : Nat := #{candidate.stride}

    def periodicDomain (period state : Nat) : Prop :=
      inferredStride ≤ period ∧ state < period

    def periodicNext (period state : Nat) : Nat :=
      (counterStep period inferredStride state).1

    def targetEvents (period initial n : Nat) : Nat :=
      #{lean(candidate.event_count)}

    def targetCost (period initial n base surcharge : Nat) : Nat :=
      #{lean(candidate.upper_bound)}

    theorem targetPeriodicBound (period initial base surcharge : Nat) (items : List Unit)
        (valid : periodicDomain period initial) :
        let model := counterRule period inferredStride base surcharge
        let result := model.run initial items
        periodicDomain period result.state ∧
          result.events = targetEvents period initial items.length ∧
          result.cost ≤ targetCost period initial items.length base surcharge := by
      have checked := counterObligations period inferredStride base surcharge (by decide) valid.1
      exact ⟨⟨valid.1, (accumulate checked initial items valid.2).1⟩,
        eventCount checked initial items valid.2, costBound checked initial items valid.2⟩

    end ReductionBounds.Periodic
    """
  end

  defp contract_source(_candidate, nil), do: ""

  defp contract_source(candidate, %Lynx.Lean{source: source}) do
    """

    namespace ReductionBounds.Periodic

    #{source}

    def targetMeasuredEvents (period initial n : Nat) : Nat :=
      #{lean(candidate.measured_event_upper_bound)}

    def targetMeasuredCost (period initial n base surcharge : Nat) : Nat :=
      #{lean(candidate.measured_upper_bound)}

    theorem targetAnnotatedBound (period initial base surcharge : Nat) (items : List Unit)
        (valid : periodicDomain period initial) (initialInv : periodicInvariant period initial) :
        let model := counterRule period inferredStride base surcharge
        let result := model.run initial items
        periodicInvariant period result.state ∧
          result.events ≤ targetMeasuredEvents period initial items.length ∧
          result.cost ≤ targetMeasuredCost period initial items.length base surcharge := by
      have checked := counterObligations period inferredStride base surcharge (by decide) valid.1
      exact annotated checked (periodicInvariant period) (periodicMeasure period)
        (fun state _ domain inv => periodicInvariantStep period state ⟨valid.1, domain⟩ inv)
        (fun state domain inv => periodicMeasureBounds period state ⟨valid.1, domain⟩ inv)
        initial items valid.2 initialInv

    open Lean in
    run_cmd do
      for dependency in ← Lean.collectAxioms ``targetAnnotatedBound do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError m!"Unexpected axiom in periodic contract: {dependency}"

    end ReductionBounds.Periodic
    """
  end

  defp add(0, right), do: right
  defp add(left, right), do: {:add, left, right}
  defp subtract(left, 0), do: left
  defp subtract(left, right), do: {:sub, left, right}
  defp multiply(left, 1), do: left
  defp multiply(left, right), do: {:mul, left, right}

  defp lean(operand) when is_integer(operand) or is_atom(operand), do: to_string(operand)
  defp lean({:measure, :periodic_measure}), do: "(periodicMeasure period initial)"
  defp lean({:add, left, right}), do: "(#{lean(left)} + #{lean(right)})"
  defp lean({:sub, left, right}), do: "(#{lean(left)} - #{lean(right)})"
  defp lean({:mul, left, right}), do: "(#{lean(left)} * #{lean(right)})"
  defp lean({:div, left, right}), do: "(#{lean(left)} / #{lean(right)})"
end
