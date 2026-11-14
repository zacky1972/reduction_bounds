defmodule ReductionBounds.ListBound do
  @moduledoc false
  # cspell:words cerl primop scrutinee succ simp cons rcases simpa

  @spec infer(term(), [binary()]) :: {:ok, map()} | {:error, term()}
  def infer({module, name, arity} = target, beams)
      when is_atom(module) and is_atom(name) and arity in [1, 2] do
    with {:ok, body} <- ReductionBounds.SearchBound.core_function(target, beams),
         {:ok, branches} <- analyze(body, {name, arity}) do
      {:ok, candidate(target, branches)}
    end
  end

  def infer(target, _beams), do: {:error, {:unsupported_target, target}}

  defp analyze({:c_fun, _, args, {:c_case, _, scrutinee, clauses}}, {_, arity} = function) do
    with true <- argument_case?(args, scrutinee),
         {fallback, clauses} when clauses != [] <- List.pop_at(clauses, -1),
         true <- fallback?(fallback),
         {:ok, branches} <- analyze_clauses(clauses, function),
         [{:empty, _, 0} | cons] <- branches,
         true <- covered_cons?(cons) do
      {:ok, branches}
    else
      _ -> {:error, {:unsupported_list_shape, arity}}
    end
  end

  defp analyze(_body, {_, arity}), do: {:error, {:unsupported_list_shape, arity}}

  defp argument_case?(args, {:c_values, _, values}), do: same_variables?(args, values)
  defp argument_case?([arg], {:c_var, _, _} = value), do: same_variables?([arg], [value])
  defp argument_case?(_args, _scrutinee), do: false

  defp same_variables?(left, right) do
    Enum.all?(left ++ right, &match?({:c_var, _, _}, &1)) and
      Enum.map(left, &:cerl.var_name/1) == Enum.map(right, &:cerl.var_name/1)
  end

  defp fallback?(
         {:c_clause, [:compiler_generated], _, {:c_literal, _, true},
          {:c_primop, _, {:c_literal, _, :match_fail}, _}}
       ),
       do: true

  defp fallback?(_clause), do: false

  defp analyze_clauses(clauses, function) do
    clauses
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, []}, fn {clause, index}, {:ok, acc} ->
      case analyze_clause(clause, index, function) do
        {:ok, branch} -> {:cont, {:ok, [branch | acc]}}
        :unsupported -> {:halt, :unsupported}
      end
    end)
    |> case do
      {:ok, branches} -> {:ok, Enum.reverse(branches)}
      :unsupported -> :unsupported
    end
  end

  defp analyze_clause({:c_clause, _, patterns, guard, body}, index, {_, arity} = function) do
    with {:ok, kind, prefix, tail} <- list_pattern(patterns, arity),
         {:ok, guard_kind} <- guard_kind(guard),
         {:ok, local, calls} <- expression_cost(body, function, prefix, tail, index),
         true <- calls <= 1 do
      # Reaching a clause includes the tests that rejected preceding clauses.
      {:ok, {branch_kind(kind, guard_kind), {:add, {:charge, index, :dispatch}, local}, calls}}
    else
      _ -> :unsupported
    end
  end

  defp list_pattern([list], 1), do: list_pattern(list, [])

  defp list_pattern([{:c_var, _, key}, list], 2),
    do: list_pattern(list, [key])

  defp list_pattern({:c_literal, _, []}, prefix) when is_list(prefix),
    do: {:ok, :empty, prefix, nil}

  defp list_pattern({:c_cons, _, {:c_var, _, head}, {:c_var, _, tail}}, prefix)
       when is_list(prefix) do
    if head != tail and head not in prefix and tail not in prefix do
      {:ok, :cons, prefix, tail}
    else
      :unsupported
    end
  end

  defp list_pattern(_pattern, _prefix), do: :unsupported

  defp guard_kind({:c_literal, _, true}), do: {:ok, :always}

  defp guard_kind({:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :"=:="}, [left, right]}) do
    if value?(left) and value?(right), do: {:ok, :guarded}, else: :unsupported
  end

  defp guard_kind(_guard), do: :unsupported

  defp branch_kind(:cons, :always), do: :cons
  defp branch_kind(:cons, :guarded), do: :guarded_cons
  defp branch_kind(:empty, :always), do: :empty
  defp branch_kind(:empty, :guarded), do: :guarded_empty

  defp covered_cons?(branches) do
    case List.pop_at(branches, -1) do
      {{:cons, _, _}, earlier} -> Enum.all?(earlier, &match?({:guarded_cons, _, _}, &1))
      _ -> false
    end
  end

  defp expression_cost({:c_let, _, [{:c_var, _, _}], first, next}, function, prefix, tail, index) do
    with {:ok, left, left_calls} <- expression_cost(first, function, prefix, tail, index),
         {:ok, right, right_calls} <- expression_cost(next, function, prefix, tail, index) do
      {:ok, {:add, left, right}, left_calls + right_calls}
    end
  end

  defp expression_cost({:c_apply, _, {:c_var, _, function}, args}, function, prefix, tail, index)
       when not is_nil(tail) do
    expected = Enum.map(prefix ++ [tail], &{:c_var, [], &1})

    if same_variables?(args, expected) do
      {:ok, {:charge, index, :recursive_call}, 1}
    else
      :unsupported
    end
  end

  defp expression_cost(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :+}, [left, right]},
         _function,
         _prefix,
         _tail,
         index
       ) do
    if value?(left) and value?(right),
      do: {:ok, {:charge, index, :addition}, 0},
      else: :unsupported
  end

  defp expression_cost(value, _function, _prefix, _tail, index) do
    if value?(value), do: {:ok, {:charge, index, :value}, 0}, else: :unsupported
  end

  defp value?({:c_var, _, _}), do: true
  defp value?({:c_literal, _, value}), do: is_boolean(value) or is_integer(value)
  defp value?(_value), do: false

  defp candidate(target, branches) do
    base = for {_kind, local, 0} <- branches, do: local
    steps = for {_kind, local, 1} <- branches, do: local

    %{
      target: target,
      domain: :proper_integer_list_with_integer_key_if_present,
      metric: :symbolic_cost,
      recurrence: branches,
      upper_bound: {:add, maximum(base), {:mul, :n, maximum(steps)}}
    }
  end

  defp maximum([]), do: 0
  defp maximum([first | rest]), do: Enum.reduce(rest, first, &{:max, &2, &1})

  @spec proof(map()) :: Lynx.Lean.t()
  def proof(%{recurrence: [{:empty, empty, 0} | cons], upper_bound: bound}) do
    stops = for {_kind, local, 0} <- cons, do: expression(local, "_charge")
    steps = for {_kind, local, 1} <- cons, do: expression(local, "_charge")

    %Lynx.Lean{
      file: "generated_list_bound.lean",
      span: {1, 1},
      indentation: 0,
      source:
        soundness_rules() <>
          """
          def listEmpty (charge : Nat → Nat → Nat) : CostExpr :=
            #{expression(empty, "charge")}

          def listStops (_charge : Nat → Nat → Nat) : List CostExpr :=
            [#{Enum.join(stops, ", ")}]

          def listSteps (_charge : Nat → Nat → Nat) : List CostExpr :=
            [#{Enum.join(steps, ", ")}]

          def listUpperBound (charge : Nat → Nat → Nat) (n : Nat) : Nat :=
            #{lean(bound)}

          theorem listCostBound (charge : Nat → Nat → Nat) (size n cost : Nat)
              (derivation : ListCost (listEmpty charge) (listStops charge) (listSteps charge) size cost)
              (sizeBound : size ≤ n) : cost ≤ listUpperBound charge n := by
            unfold listUpperBound
            apply listRulesSound derivation sizeBound
            · simp [listEmpty, CostExpr.eval] <;> omega
            · intro branch member
              simp [listStops] at member <;>
              #{branch_cases(stops, "CostExpr.eval")}
            · intro branch member
              simp [listSteps] at member <;>
              #{branch_cases(steps, "CostExpr.eval, CostExpr.calls")}
          """
    }
  end

  defp branch_cases([], _rules), do: "contradiction"
  defp branch_cases([_], rules), do: "subst branch; simp [#{rules}] <;> omega"

  defp branch_cases(branches, rules) do
    alternatives = Enum.map_join(branches, " | ", fn _ -> "rfl" end)
    "rcases member with #{alternatives} <;> simp [#{rules}] <;> omega"
  end

  defp soundness_rules() do
    """
    inductive CostExpr where
      | paid : Nat → CostExpr
      | seq : CostExpr → CostExpr → CostExpr
      | tail : CostExpr

    def CostExpr.eval (tailCost : Nat) : CostExpr → Nat
      | .paid cost => cost
      | .seq left right => left.eval tailCost + right.eval tailCost
      | .tail => tailCost

    def CostExpr.calls : CostExpr → Nat
      | .paid _ => 0
      | .seq left right => left.calls + right.calls
      | .tail => 1

    theorem costComposition (expr : CostExpr) (tailCost : Nat) :
        expr.eval tailCost = expr.eval 0 + expr.calls * tailCost := by
      induction expr with
      | paid cost => simp [CostExpr.eval, CostExpr.calls]
      | seq left right leftIH rightIH =>
        simp only [CostExpr.eval, CostExpr.calls, Nat.add_mul, leftIH, rightIH]
        omega
      | tail => simp [CostExpr.eval, CostExpr.calls]

    inductive ListCost (empty : CostExpr) (stops steps : List CostExpr) : Nat → Nat → Prop where
      | nil : ListCost empty stops steps 0 (empty.eval 0)
      | stop {size branch} : branch ∈ stops →
          ListCost empty stops steps (size + 1) (branch.eval 0)
      | step {size branch tailCost} : branch ∈ steps →
          ListCost empty stops steps size tailCost →
          ListCost empty stops steps (size + 1) (branch.eval tailCost)

    theorem listRulesSound {empty stops steps size cost n base step}
        (derivation : ListCost empty stops steps size cost) (sizeBound : size ≤ n)
        (emptyBound : empty.eval 0 ≤ base)
        (stopBound : ∀ branch ∈ stops, branch.eval 0 ≤ base)
        (stepBound : ∀ branch ∈ steps, branch.eval 0 ≤ step ∧ branch.calls ≤ 1) :
        cost ≤ base + n * step := by
      have exactBound : cost ≤ base + size * step := by
        induction derivation with
        | nil => simpa using emptyBound
        | stop member =>
          exact Nat.le_trans (stopBound _ member) (Nat.le_add_right _ _)
        | @step size branch tailCost member _ ih =>
          obtain ⟨localBound, countBound⟩ := stepBound branch member
          have recursiveBound := Nat.mul_le_mul_right tailCost countBound
          rw [Nat.one_mul] at recursiveBound
          have tailBound := ih (by omega : size ≤ n)
          rw [costComposition, Nat.succ_mul]
          omega
      exact Nat.le_trans exactBound
        (Nat.add_le_add_left (Nat.mul_le_mul_right step sizeBound) _)

    """
  end

  defp expression({:add, left, right}, charges),
    do: "(.seq #{expression(left, charges)} #{expression(right, charges)})"

  defp expression({:charge, _, :recursive_call} = charge, charges),
    do: "(.seq (.paid #{lean(charge, charges)}) .tail)"

  defp expression(charge, charges), do: "(.paid #{lean(charge, charges)})"

  defp lean(expr), do: lean(expr, "charge")

  defp lean({:add, left, right}, charges),
    do: "(#{lean(left, charges)} + #{lean(right, charges)})"

  defp lean({:mul, left, right}, charges),
    do: "(#{lean(left, charges)} * #{lean(right, charges)})"

  defp lean({:max, left, right}, charges),
    do: "(max #{lean(left, charges)} #{lean(right, charges)})"

  defp lean({:charge, index, :dispatch}, charges), do: "(#{charges} #{index} 0)"
  defp lean({:charge, index, :value}, charges), do: "(#{charges} #{index} 1)"
  defp lean({:charge, index, :recursive_call}, charges), do: "(#{charges} #{index} 2)"
  defp lean({:charge, index, :addition}, charges), do: "(#{charges} #{index} 3)"
  defp lean(:n, _charges), do: "n"
  defp lean(0, _charges), do: "0"
end
