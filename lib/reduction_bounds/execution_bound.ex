defmodule ReductionBounds.ExecutionBound do
  @moduledoc false

  alias ReductionBounds.{CoreFragment, ProofInput, SearchBound}

  @type cost ::
          non_neg_integer()
          | :previous
          | {:charge, atom()}
          | {:contract, ReductionBounds.target()}
          | {:add, cost(), cost()}
          | {:max, cost(), cost()}

  @spec infer(ReductionBounds.target(), [binary()], %{
          ReductionBounds.target() => non_neg_integer()
        }) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer({_, _, 1} = target, beams, contracts) do
    with {:ok, core} <- SearchBound.core_function(target, beams),
         {:ok, program} <- decode(core, target) do
      build(target, program, contracts)
    end
  end

  def infer(target, _beams, _contracts), do: {:error, {:unsupported_target, target}}

  defp decode({:c_fun, _, [parameter], body}, target) do
    with {:ok, name} <- CoreFragment.variable_name(parameter),
         {:ok, subject, zero, binder, positive} <- zero_case(body),
         {:ok, ^name} <- CoreFragment.variable_name(subject),
         {:ok, zero} <- expression(zero, MapSet.new([name]), target),
         {:ok, positive} <- expression(positive, MapSet.new([name, binder]), target) do
      {:ok, {name, binder, zero, positive}}
    else
      {:error, _reason} = error -> error
      _ -> unsupported(body, :expected_zero_and_default_clauses)
    end
  end

  defp decode(core, _target), do: unsupported(core, :expected_unary_function)

  defp zero_case(
         {:c_case, _, subject,
          [
            {:c_clause, _, [{:c_literal, _, 0}], {:c_literal, _, true}, zero},
            {:c_clause, _, [variable], {:c_literal, _, true}, positive}
          ]}
       ) do
    with {:ok, binder} <- CoreFragment.variable_name(variable) do
      {:ok, subject, zero, binder, positive}
    end
  end

  defp zero_case(_core), do: :unsupported

  defp expression({:c_let, _, [variable], rhs, body}, env, target) do
    with {:ok, name} <- CoreFragment.variable_name(variable),
         {:ok, rhs} <- expression(rhs, env, target),
         {:ok, body} <- expression(body, MapSet.put(env, name), target) do
      {:ok, {:bind, name, rhs, body}}
    end
  end

  defp expression({:c_case, _, _, _} = core, env, target) do
    with {:ok, subject, zero, binder, positive} <- zero_case(core),
         {:ok, subject} <- expression(subject, env, target),
         {:ok, zero} <- expression(zero, env, target),
         {:ok, positive} <- expression(positive, MapSet.put(env, binder), target) do
      {:ok, {:if_zero, subject, zero, binder, positive}}
    else
      {:error, _reason} = error -> error
      _ -> unsupported(core, :expected_zero_and_default_clauses)
    end
  end

  defp expression(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :-}, [left, {:c_literal, _, 1}]},
         env,
         _target
       ) do
    with {:ok, operand} <- operand(left, env), do: {:ok, {:predecessor, operand}}
  end

  defp expression(
         {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :+}, [left, right]},
         env,
         _target
       ) do
    with {:ok, left} <- operand(left, env),
         {:ok, right} <- operand(right, env),
         do: {:ok, {:add, left, right}}
  end

  defp expression(
         {:c_apply, _, {:c_var, _, {name, 1}}, [argument]},
         env,
         {_, name, 1}
       ) do
    with {:ok, argument} <- operand(argument, env), do: {:ok, {:recur, argument}}
  end

  defp expression(
         {:c_call, _, {:c_literal, _, module}, {:c_literal, _, fun}, [argument]},
         env,
         target
       )
       when is_atom(module) and is_atom(fun) do
    callee = {module, fun, 1}

    with {:ok, argument} <- operand(argument, env) do
      if callee == target, do: {:ok, {:recur, argument}}, else: {:ok, {:call, callee, argument}}
    end
  end

  defp expression(core, env, _target) do
    with {:ok, value} <- operand(core, env), do: {:ok, {:value, value}}
  end

  defp operand({:c_literal, _, n}, _env) when is_integer(n) and n >= 0, do: {:ok, {:literal, n}}

  defp operand({:c_var, _, _} = core, env) do
    with {:ok, name} <- CoreFragment.variable_name(core), do: variable(name, env)
  end

  defp operand(core, _env), do: unsupported(core, :unsupported_expression)

  defp variable(name, env) do
    if MapSet.member?(env, name),
      do: {:ok, {:local, name}},
      else: unsupported(name, :unbound_variable)
  end

  defp unsupported(node, reason), do: {:error, {:unsupported_core, reason, node}}

  defp build(target, {_, _, zero, positive} = program, contracts) do
    {base, base_calls} = summarize(zero)
    {step, step_calls} = summarize(positive)
    calls = Enum.uniq(base_calls ++ step_calls)
    missing = Enum.reject(calls, &Map.has_key?(contracts, &1))

    if missing == [] do
      candidate = %{
        target: target,
        source: :execution_fragment,
        metric: :symbolic_cost,
        precondition: {:nonnegative_integer, 0},
        call_contracts: Map.take(contracts, calls),
        upper_bound: %{zero: charge(:branch, base), successor: charge(:branch, step)},
        termination: :under_call_contracts
      }

      {:ok, candidate, proof(candidate, program)}
    else
      {:error, {:unresolved_call_contracts, missing}}
    end
  end

  defp charge(operation, cost), do: {:add, {:charge, operation}, cost}

  defp summarize({:value, _}), do: {0, []}
  defp summarize({:predecessor, _}), do: {{:charge, :subtract}, []}
  defp summarize({:add, _, _}), do: {{:charge, :add}, []}
  defp summarize({:call, target, _}), do: {charge(:call, {:contract, target}), [target]}
  defp summarize({:recur, _}), do: {charge(:recursive_call, :previous), []}
  defp summarize({:bind, _, rhs, body}), do: combine(:bind, :add, rhs, body)

  defp summarize({:if_zero, test, yes, _, no}) do
    {test_cost, test_calls} = summarize(test)
    {yes_cost, yes_calls} = summarize(yes)
    {no_cost, no_calls} = summarize(no)

    {charge(:branch, {:add, test_cost, {:max, yes_cost, no_cost}}),
     test_calls ++ yes_calls ++ no_calls}
  end

  defp combine(operation, combiner, left, right) do
    {left, left_calls} = summarize(left)
    {right, right_calls} = summarize(right)
    {charge(operation, {combiner, left, right}), left_calls ++ right_calls}
  end

  defp proof(
         %{upper_bound: %{zero: zero_cost, successor: step_cost}, call_contracts: contracts},
         {name, binder, zero, positive}
       ) do
    source = """
    namespace ReductionBounds.Execution

    def targetProgram : Program := ⟨#{string(name)}, #{string(binder)}, #{emit(zero)}, #{emit(positive)}⟩

    def targetContracts : List (String × Nat) := [#{contract_source(contracts)}]

    def targetCaps (name : String) : Nat :=
      (targetContracts.lookup name).getD 0

    def targetStep (charge : Charges) (_previous : Nat) : Nat :=
      #{cost(step_cost, "_previous")}

    def targetUpper (charge : Charges) : Nat → Nat
      | 0 => #{cost(zero_cost, "0")}
      | n + 1 => targetStep charge (targetUpper charge n)

    theorem targetValid : targetProgram.valid = true := by decide

    theorem targetScoped : targetProgram.scoped = true := by decide

    theorem targetCallsCovered :
        targetProgram.callees.all (fun name => (targetContracts.lookup name).isSome) = true :=
      by decide

    theorem targetStepCorrect (charge : Charges) (previous : Nat) :
        targetStep charge previous = charge "branch" +
          (targetProgram.positive.tree charge targetCaps previous).upperBound := by rfl

    theorem targetUpperCorrect (charge : Charges) (n : Nat) :
        targetUpper charge n = targetProgram.upper charge targetCaps n := by
      induction n with
      | zero => rfl
      | succ n ih =>
        simp only [targetUpper, Program.upper, targetStepCorrect, ih]

    theorem targetCostBound (charge : Charges) (external : Callee)
        (contracts : CallBounds external targetCaps targetProgram.callees)
        (n result actual : Nat) (run : targetProgram.runs charge external n result actual) :
        actual ≤ targetUpper charge n := by
      rw [targetUpperCorrect]
      exact targetProgram.bounded charge targetCaps external targetValid contracts n result actual run

    theorem targetTerminates (charge : Charges) (external : Callee)
        (contracts : CallTotal external targetProgram.callees) (n : Nat) :
        ∃ result actual, targetProgram.runsAt charge external (n + 1) n result actual :=
      targetProgram.terminates charge external targetValid contracts n

    end ReductionBounds.Execution
    """

    %Lynx.Lean{
      file: "generated_execution_bound.lean",
      span: {1, 1},
      indentation: 0,
      source: source
    }
  end

  defp contract_source(contracts) do
    Enum.map_join(Enum.sort(contracts), ", ", fn {callee, bound} ->
      "(#{id(callee)}, #{bound})"
    end)
  end

  defp emit({:value, operand}), do: "(Expr.value #{read(operand)})"
  defp emit({:predecessor, operand}), do: "(Expr.predecessor #{read(operand)})"
  defp emit({:add, left, right}), do: "(Expr.add #{read(left)} #{read(right)})"

  defp emit({:bind, name, rhs, body}),
    do: "(Expr.letIn #{string(name)} #{emit(rhs)} #{emit(body)})"

  defp emit({:if_zero, test, yes, name, no}),
    do: "(Expr.ifZero #{emit(test)} #{emit(yes)} #{string(name)} #{emit(no)})"

  defp emit({:call, target, value}), do: "(Expr.call #{id(target)} #{read(value)})"
  defp emit({:recur, argument}), do: "(Expr.recur #{read(argument)})"

  defp read({:local, name}), do: "(Operand.local #{string(name)})"
  defp read({:literal, value}), do: "(Operand.literal #{value})"

  defp cost(0, _previous), do: "0"
  defp cost(:previous, previous), do: previous
  defp cost({:charge, name}, _previous), do: "(charge #{string(Atom.to_string(name))})"
  defp cost({:contract, callee}, _previous), do: "(targetCaps #{id(callee)})"

  defp cost({:add, left, right}, previous),
    do: "(#{cost(left, previous)} + #{cost(right, previous)})"

  defp cost({:max, left, right}, previous),
    do: "(max #{cost(left, previous)} #{cost(right, previous)})"

  defp id(target), do: string(inspect(target, limit: :infinity, printable_limit: :infinity))
  defp string(value), do: ProofInput.string(value)
end
