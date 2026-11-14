defmodule ReductionBounds.ListBound do
  @moduledoc false
  # cspell:words cerl primop scrutinee succ

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
    cons_cost = for {_kind, local, calls} <- cons, do: with_recursion(local, calls)

    %Lynx.Lean{
      file: "generated_list_bound.lean",
      span: {1, 1},
      indentation: 0,
      source: """
      def listCost (charge : Nat → Nat → Nat) : Nat → Nat
        | 0 => #{lean(empty)}
        | n + 1 => #{lean(maximum(cons_cost))}

      def listUpperBound (charge : Nat → Nat → Nat) (n : Nat) : Nat :=
        #{lean(bound)}

      theorem listCostBound (charge : Nat → Nat → Nat) (size n : Nat)
          (sizeBound : size ≤ n) : listCost charge size ≤ listUpperBound charge n := by
        have exactBound (k : Nat) : listCost charge k ≤ listUpperBound charge k := by
          induction k with
          | zero =>
              simp only [listCost, listUpperBound, Nat.zero_mul, Nat.add_zero]
              omega
          | succ k ih =>
              simp only [listCost, listUpperBound, Nat.succ_mul] at *
              omega
        refine Nat.le_trans (exactBound size) ?_
        unfold listUpperBound
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ sizeBound) _
      """
    }
  end

  defp with_recursion(local, 0), do: local
  defp with_recursion(local, 1), do: {:add, local, :tail_cost}

  defp lean({:add, left, right}), do: "(#{lean(left)} + #{lean(right)})"
  defp lean({:mul, left, right}), do: "(#{lean(left)} * #{lean(right)})"
  defp lean({:max, left, right}), do: "(max #{lean(left)} #{lean(right)})"
  defp lean({:charge, index, :dispatch}), do: "(charge #{index} 0)"
  defp lean({:charge, index, :value}), do: "(charge #{index} 1)"
  defp lean({:charge, index, :recursive_call}), do: "(charge #{index} 2)"
  defp lean({:charge, index, :addition}), do: "(charge #{index} 3)"
  defp lean(:tail_cost), do: "(listCost charge n)"
  defp lean(:n), do: "n"
  defp lean(0), do: "0"
end
