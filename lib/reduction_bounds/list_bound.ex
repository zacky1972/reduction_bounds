defmodule ReductionBounds.ListBound do
  @moduledoc false
  # cspell:words cerl primop scrutinee succ simp cons rcases simpa leanj symm nonzero elim propext

  @spec infer(term(), [binary()]) :: {:ok, map()} | {:error, term()}
  def infer({:lists, :member, 2} = target, _beams) do
    branches = [
      {:empty, {:add, {:charge, 0, :dispatch}, {:charge, 0, :value}}, 0},
      {:guarded_cons, {:add, {:charge, 1, :dispatch}, {:charge, 1, :value}}, 0},
      {:cons, {:add, {:charge, 2, :dispatch}, {:charge, 2, :recursive_call}}, 1}
    ]

    {:ok,
     Map.merge(candidate(target, branches), %{value_model: :membership, source: :lynx_builtin})}
  end

  def infer({module, name, arity} = target, beams)
      when is_atom(module) and is_atom(name) and arity in [1, 2] do
    with {:ok, body} <- ReductionBounds.SearchBound.core_function(target, beams),
         {:ok, branches} <- analyze(body, {name, arity}) do
      {:ok, Map.put(candidate(target, branches), :value_model, value_model(body, target))}
    end
  end

  def infer(target, _beams), do: {:error, {:unsupported_target, target}}

  @spec check_forwarding_call(term(), term(), [binary()]) :: :ok | {:error, term()}
  def check_forwarding_call({module, caller, arity}, {module, callee, arity}, beams)
      when is_atom(module) and is_atom(caller) and is_atom(callee) and
             caller != callee and arity in [1, 2] do
    with {:ok, {:c_fun, _, params, {:c_apply, _, {:c_var, _, {^callee, ^arity}}, args}}} <-
           ReductionBounds.SearchBound.core_function({module, caller, arity}, beams),
         true <- same_variables?(params, args) do
      :ok
    else
      {:error, _reason} = error -> error
      _ -> {:error, :unsupported_forwarding_call}
    end
  end

  def check_forwarding_call(_caller, _callee, _beams), do: {:error, :unsupported_forwarding_call}

  defp value_model(body, {_, name, 2}) do
    if ReductionBounds.SearchBound.search_body?(body, name), do: :membership
  end

  defp value_model(
         {:c_fun, _, _,
          {:c_case, _, _,
           [
             {:c_clause, _, _, _, {:c_literal, _, 0}},
             {:c_clause, _, [{:c_cons, _, _, {:c_var, _, tail}}], _,
              {:c_let, _, [{:c_var, _, result}],
               {:c_apply, _, {:c_var, _, {name, 1}}, [{:c_var, _, tail}]},
               {:c_call, _, _, _, [{:c_literal, _, 1}, {:c_var, _, result}]}}},
             _fallback
           ]}},
         {_, name, 1}
       ),
       do: :length

  defp value_model(_body, _target), do: nil

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
    [{:empty, empty, 0} | cons] = branches
    stops = for {_kind, local, 0} <- cons, do: local
    step = maximum(steps)

    %{
      target: target,
      domain: :proper_integer_list_with_integer_key_if_present,
      metric: :symbolic_cost,
      recurrence: branches,
      upper_bound: {:add, maximum(base), {:mul, :n, step}},
      refined_upper_bound: refined_bound(empty, stops, step)
    }
  end

  defp refined_bound(empty, [], step), do: {:add, empty, {:mul, :n, step}}

  defp refined_bound(empty, stops, step) do
    empty_path = {:add, empty, {:mul, :n, step}}
    stop_path = {:add, maximum(stops), {:mul, {:sub, :n, 1}, step}}
    {:if_zero, :n, empty, {:max, empty_path, stop_path}}
  end

  defp maximum([]), do: 0
  defp maximum([first | rest]), do: Enum.reduce(rest, first, &{:max, &2, &1})

  @spec proof(map()) :: Lynx.Lean.t()
  def proof(%{recurrence: [{:empty, empty, 0} | cons], upper_bound: bound} = candidate) do
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
          """ <> refined_proof(candidate) <> value_proof(candidate)
    }
  end

  @spec input_proof(map(), Lynx.Lean.t() | nil) :: {:ok, Lynx.Lean.t()} | {:error, atom()}
  def input_proof(candidate, nil), do: {:ok, proof(candidate)}

  def input_proof(%{value_model: nil}, %Lynx.Lean{}),
    do: {:error, :unsupported_value_model}

  def input_proof(candidate, %Lynx.Lean{source: source}) do
    proof = proof(candidate)

    source =
      proof.source <>
        "\n" <>
        source <>
        "\n" <>
        input_rules() <>
        input_bound(candidate) <> audit("listInputValueAndBound")

    {:ok, %{proof | source: source}}
  end

  @spec forwarding_proof(ReductionBounds.target(), map(), Lynx.Lean.t() | nil) ::
          {:ok, Lynx.Lean.t()} | {:error, atom()}
  def forwarding_proof(_caller, %{value_model: nil}, _contract),
    do: {:error, :unsupported_value_model}

  def forwarding_proof(caller, %{value_model: kind, target: callee} = candidate, contract) do
    with {:ok, proof} <- input_proof(candidate, contract) do
      source = forwarding_rules(caller, callee, kind, contract)
      {:ok, %{proof | source: proof.source <> source <> audit("listCallerValueAndBound")}}
    end
  end

  defp audit(theorem) do
    """
    open Lean in
    run_cmd do
      for dependency in ← Lean.collectAxioms ``#{theorem} do
        unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
          throwError m!"Unexpected axiom in #{theorem}: {dependency}"
    """
  end

  defp input_rules() do
    """
    theorem inputLengthBound (xs : List Int) (invariant : inputInvariant xs) :
        xs.length ≤ inputSize xs := by
      induction xs with
      | nil => exact Nat.zero_le _
      | cons head tail ih =>
        have tailInvariant := inputInvariantTail head tail invariant
        have smaller := inputSizeTail head tail invariant
        simp only [List.length_cons]
        exact Nat.le_trans (Nat.succ_le_succ (ih tailInvariant)) smaller
    """
  end

  defp input_bound(%{value_model: kind, target: target}) do
    {key, arguments, value, cost, theorem_args} = model_terms(kind)

    """
    theorem listInputValueAndBound (charge : Nat → Nat → Nat) #{key} (xs : List Int)
        (precondition : inputPrecondition xs) :
        #{lean_function(target)} #{arguments} = .ok #{value} ∧
        #{cost} ≤ listRefinedUpperBound charge (inputSize xs) := by
      have bound := inputLengthBound xs (inputInvariantInit xs precondition)
      have result := listValueAndBound charge #{theorem_args} (inputSize xs) bound
      exact ⟨result.1, result.2.2⟩
    """
  end

  defp forwarding_rules(caller, callee, kind, contract) do
    {key, arguments, value, cost, theorem_args} = model_terms(kind)

    {size, premises, callee_result, callee_bound} =
      if is_nil(contract) do
        {"n", "(n : Nat) (sizeBound : xs.length ≤ n)",
         "listValueAndBound charge #{theorem_args} n sizeBound", "calleeResult.2.2"}
      else
        {"(inputSize xs)", "(precondition : inputPrecondition xs)",
         "listInputValueAndBound charge #{theorem_args} precondition", "calleeResult.2"}
      end

    """
    theorem listCallerValueAndBound (charge : Nat → Nat → Nat) (callerCost : Nat)
        #{key} (xs : List Int) #{premises} :
        #{lean_function(caller)} #{arguments} = .ok #{value} ∧
        callerCost + #{cost} ≤ callerCost + listRefinedUpperBound charge #{size} := by
      have calleeResult := #{callee_result}
      change #{lean_function(callee)} #{arguments} = .ok #{value} ∧ _
      exact ⟨calleeResult.1, Nat.add_le_add_left #{callee_bound} callerCost⟩
    """
  end

  defp model_terms(:length) do
    {"", "(integerListTerm xs)", "(.integer (costedLength charge xs).1)",
     "(costedLength charge xs).2", "xs"}
  end

  defp model_terms(:membership) do
    {"(key : Int)", "(.integer key) (integerListTerm xs)", "(costedSearch charge key xs).1",
     "(costedSearch charge key xs).2", "key xs"}
  end

  defp lean_function({module, name, arity}) do
    "#{:lynx_core_to_leanj.module_name(module)}.«#{name}/#{arity}»"
  end

  defp refined_proof(%{recurrence: [{:empty, empty, 0} | cons], refined_upper_bound: bound}) do
    stops = for {_kind, local, 0} <- cons, do: expression(local, "_charge")
    stop_costs = for {_kind, local, 0} <- cons, do: local
    steps = for {_kind, local, 1} <- cons, do: expression(local, "_charge")
    step_costs = for {_kind, local, 1} <- cons, do: local

    """
    def listRefinedUpperBound (charge : Nat → Nat → Nat) (n : Nat) : Nat :=
      #{lean(bound)}

    theorem listRefinedCostBound (charge : Nat → Nat → Nat) (size n cost : Nat)
        (derivation : ListCost (listEmpty charge) (listStops charge) (listSteps charge) size cost)
        (sizeBound : size ≤ n) : cost ≤ listRefinedUpperBound charge n := by
      have paths := listPathBounds (stop := #{lean(maximum(stop_costs))})
        (step := #{lean(maximum(step_costs))}) derivation
      have stopBound : ∀ branch ∈ listStops charge,
          branch.eval 0 ≤ #{lean(maximum(stop_costs))} := by
        intro branch member
        simp [listStops] at member <;>
        #{branch_cases(stops, "CostExpr.eval")}
      have stepBound : ∀ branch ∈ listSteps charge,
          branch.eval 0 ≤ #{lean(maximum(step_costs))} ∧ branch.calls ≤ 1 := by
        intro branch member
        simp [listSteps] at member <;>
        #{branch_cases(steps, "CostExpr.eval, CostExpr.calls")}
      rcases paths stopBound stepBound with emptyPath | ⟨hasStop, positive, stopPath⟩
      · have bound := Nat.le_trans emptyPath
          (Nat.add_le_add_left (Nat.mul_le_mul_right _ sizeBound) ((listEmpty charge).eval 0))
        #{refined_empty_case(empty, stops)}
      · #{refined_stop_case(stops)}
    """
  end

  defp refined_empty_case(_empty, []),
    do: "simpa [listRefinedUpperBound, listEmpty, CostExpr.eval] using bound"

  defp refined_empty_case(empty, [_ | _]) do
    """
    by_cases zero : n = 0
        · simpa [listRefinedUpperBound, zero, listEmpty, CostExpr.eval] using bound
        · simp only [listRefinedUpperBound, if_neg zero]
          exact Nat.le_trans
            (by simpa [listEmpty, CostExpr.eval] using bound :
              cost ≤ #{lean(empty)} + n * _)
            (Nat.le_max_left _ _)
    """
  end

  defp refined_stop_case([]), do: "exact False.elim (hasStop rfl)"

  defp refined_stop_case([_ | _]) do
    """
    have nonzero : n ≠ 0 := by omega
        simp only [listRefinedUpperBound, if_neg nonzero]
        exact Nat.le_trans stopPath
          (Nat.le_trans (Nat.add_le_add_left
            (Nat.mul_le_mul_right _ (Nat.sub_le_sub_right sizeBound 1)) _)
            (Nat.le_max_right _ _))
    """
  end

  defp value_proof(%{value_model: nil}), do: ""

  defp value_proof(%{value_model: kind, target: target}) do
    """
    def integerListTerm : List Int → Lynx.Term
      | [] => .nil
      | head :: tail => .cons (.integer head) (integerListTerm tail)

    """ <> value_proof(kind, lean_function(target), target)
  end

  defp value_proof(:length, function, _target) do
    """
    def costedLength (charge : Nat → Nat → Nat) : List Int → Int × Nat
      | [] => (0, (listEmpty charge).eval 0)
      | _ :: tail =>
        let result := costedLength charge tail
        (1 + result.1, charge 1 0 + (charge 1 2 + result.2) + charge 1 3)

    theorem listValueAgreement (charge : Nat → Nat → Nat) (xs : List Int) :
        #{function} (integerListTerm xs) = .ok (.integer (costedLength charge xs).1) := by
      induction xs with
      | nil =>
        rw [integerListTerm, #{function}.eq_def]
        rfl
      | cons head tail ih =>
        rw [integerListTerm, #{function}.eq_def]
        simp only [ih, costedLength]
        rfl

    theorem lengthCostDerivation (charge : Nat → Nat → Nat) (xs : List Int) :
        ListCost (listEmpty charge) (listStops charge) (listSteps charge)
          xs.length (costedLength charge xs).2 := by
      induction xs with
      | nil => exact .nil
      | cons head tail ih =>
        simp only [List.length_cons, costedLength]
        have stepDerivation := ListCost.step
          (empty := listEmpty charge) (stops := listStops charge) (steps := listSteps charge)
          (branch := (.seq (.paid (charge 1 0))
            (.seq (.seq (.paid (charge 1 2)) .tail) (.paid (charge 1 3)))))
          (by simp [listSteps]) ih
        simpa [CostExpr.eval, Nat.add_assoc] using stepDerivation

    theorem listValueAndBound (charge : Nat → Nat → Nat) (xs : List Int) (n : Nat)
        (sizeBound : xs.length ≤ n) :
        #{function} (integerListTerm xs) = .ok (.integer (costedLength charge xs).1) ∧
        (costedLength charge xs).2 ≤ listUpperBound charge n ∧
        (costedLength charge xs).2 ≤ listRefinedUpperBound charge n :=
      ⟨listValueAgreement charge xs,
        listCostBound charge xs.length n _ (lengthCostDerivation charge xs) sizeBound,
        listRefinedCostBound charge xs.length n _ (lengthCostDerivation charge xs) sizeBound⟩
    """
  end

  defp value_proof(:membership, function, target) do
    """
    def costedSearch (charge : Nat → Nat → Nat) (key : Int) : List Int → Lynx.Term × Nat
      | [] => (.atom "false", (listEmpty charge).eval 0)
      | head :: tail =>
        if head = key then (.atom "true", charge 1 0 + charge 1 1)
        else
          let result := costedSearch charge key tail
          (result.1, charge 2 0 + (charge 2 2 + result.2))

    theorem listValueAgreement (charge : Nat → Nat → Nat) (key : Int) (xs : List Int) :
        #{function} (.integer key) (integerListTerm xs) = .ok (costedSearch charge key xs).1 := by
    #{membership_agreement(target, function)}
    theorem searchCostDerivation (charge : Nat → Nat → Nat) (key : Int) (xs : List Int) :
        ListCost (listEmpty charge) (listStops charge) (listSteps charge)
          xs.length (costedSearch charge key xs).2 := by
      induction xs with
      | nil => exact .nil
      | cons head tail ih =>
        by_cases equal : head = key
        · simp only [List.length_cons, costedSearch, if_pos equal]
          exact ListCost.stop (branch := .seq (.paid (charge 1 0)) (.paid (charge 1 1)))
            (by simp [listStops])
        · simp only [List.length_cons, costedSearch, if_neg equal]
          exact ListCost.step (branch := .seq (.paid (charge 2 0)) (.seq (.paid (charge 2 2)) .tail))
            (by simp [listSteps]) ih

    theorem listValueAndBound (charge : Nat → Nat → Nat) (key : Int) (xs : List Int) (n : Nat)
        (sizeBound : xs.length ≤ n) :
        #{function} (.integer key) (integerListTerm xs) = .ok (costedSearch charge key xs).1 ∧
        (costedSearch charge key xs).2 ≤ listUpperBound charge n ∧
        (costedSearch charge key xs).2 ≤ listRefinedUpperBound charge n :=
      ⟨listValueAgreement charge key xs,
        listCostBound charge xs.length n _ (searchCostDerivation charge key xs) sizeBound,
        listRefinedCostBound charge xs.length n _ (searchCostDerivation charge key xs) sizeBound⟩
    """
  end

  defp membership_agreement({:lists, :member, 2}, function) do
    """
      induction xs with
      | nil => rfl
      | cons head tail ih =>
        rw [integerListTerm, #{function}.eq_def]
        by_cases equal : head = key
        · simp [costedSearch, equal, Lynx.Term.true]
        · simp [costedSearch, equal, Ne.symm equal, ih]
    """
  end

  defp membership_agreement(_target, function) do
    """
      induction xs with
      | nil =>
        rw [integerListTerm, #{function}.eq_def]
        rfl
      | cons head tail ih =>
        rw [integerListTerm, #{function}.eq_def]
        by_cases equal : head = key
        · simp [costedSearch, equal, Erlang.erlang.«=:=/2», Lynx.Except.guard_ok]
        · simp [costedSearch, equal, Ne.symm equal, Erlang.erlang.«=:=/2», Lynx.Except.guard_ok, ih]
    """
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

    theorem listPathBounds {empty stops steps size cost stop step}
        (derivation : ListCost empty stops steps size cost)
        (stopBound : ∀ branch ∈ stops, branch.eval 0 ≤ stop)
        (stepBound : ∀ branch ∈ steps, branch.eval 0 ≤ step ∧ branch.calls ≤ 1) :
        cost ≤ empty.eval 0 + size * step ∨
          (stops ≠ [] ∧ 0 < size ∧ cost ≤ stop + (size - 1) * step) := by
      induction derivation with
      | nil => exact Or.inl (by simp)
      | @stop size branch member =>
        right
        refine ⟨?_, by omega, ?_⟩
        · intro noStops
          simp [noStops] at member
        · exact Nat.le_trans (stopBound branch member) (Nat.le_add_right _ _)
      | @step size branch tailCost member _ ih =>
        obtain ⟨localBound, countBound⟩ := stepBound branch member
        have recursiveBound := Nat.mul_le_mul_right tailCost countBound
        rw [Nat.one_mul] at recursiveBound
        rw [costComposition]
        rcases ih with emptyPath | ⟨hasStop, positive, stopPath⟩
        · left
          rw [Nat.succ_mul]
          omega
        · right
          refine ⟨hasStop, by omega, ?_⟩
          have sizeEq : size = (size - 1) + 1 := by omega
          have sizeCost : size * step = (size - 1) * step + step := by
            conv => lhs; rw [sizeEq]
            rw [Nat.succ_mul]
          simp only [Nat.add_sub_cancel]
          omega

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

  defp lean({:sub, left, right}, charges),
    do: "(#{lean(left, charges)} - #{lean(right, charges)})"

  defp lean({:if_zero, size, empty, nonempty}, charges),
    do:
      "(if #{lean(size, charges)} = 0 then #{lean(empty, charges)} else #{lean(nonempty, charges)})"

  defp lean(1, _charges), do: "1"
  defp lean(:n, _charges), do: "n"
  defp lean(0, _charges), do: "0"
end
