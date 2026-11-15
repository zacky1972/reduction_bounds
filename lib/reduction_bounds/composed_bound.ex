defmodule ReductionBounds.ComposedBound do
  @moduledoc false
  # cspell:words cerl leanj simp simpa cons primop

  alias ReductionBounds.{CoreFragment, ListBound, Normalize, ProofInput, SearchBound}

  @member {:lists, :member, 2}
  @reverse {:lists, :reverse, 2}
  @buffer_charges %{consume: 0, fill: 1, rotate: 2, zero: 3, enum_reverse: 4}

  @spec infer_struct(ReductionBounds.target(), [binary()]) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def infer_struct(target, beams) do
    with {:ok, core} <- SearchBound.core_function(target, beams),
         {:ok, program} <- CoreFragment.decode(core) do
      normalized = Normalize.normalize(program)
      upper_bound = struct_bound(program.expression)

      candidate = %{
        target: target,
        source: :struct_fragment,
        metric: :symbolic_cost,
        upper_bound: upper_bound,
        opaque_paths: Map.keys(program.opaque) |> Enum.sort(),
        normalization: normalized
      }

      {:ok, candidate, struct_proof(program.expression, upper_bound, normalized.certificates)}
    end
  end

  defp struct_bound({kind, _}) when kind in [:var, :int, :atom], do: 0
  defp struct_bound({:opaque, id}), do: {:opaque_cost, id}

  defp struct_bound({:let_in, _, rhs, body}),
    do: add({:operation_cost, :bind}, add(struct_bound(rhs), struct_bound(body)))

  defp struct_bound({:case_map, subject, _, matched, fallback}) do
    map_branch_bound(subject, struct_bound(matched), struct_bound(fallback))
  end

  defp struct_bound({:case_map_guarded, subject, _, condition, matched, fallback}) do
    fallback_bound = struct_bound(fallback)
    matched_bound = guard_bound(condition, struct_bound(matched), fallback_bound)
    map_branch_bound(subject, matched_bound, fallback_bound)
  end

  defp struct_bound({:guarded, condition, success, failure}),
    do: guard_bound(condition, struct_bound(success), struct_bound(failure))

  defp struct_bound({operation, operand}) when operation in [:is_integer, :is_map],
    do: add(struct_bound(operand), {:operation_cost, operation})

  defp struct_bound({:field, subject, _key}),
    do: add(struct_bound(subject), {:operation_cost, :field})

  defp struct_bound({:update, subject, _key, rhs}),
    do: struct_binary_bound(:update, subject, rhs)

  defp struct_bound({operation, left, right}) when operation in [:ge, :sub],
    do: struct_binary_bound(operation, left, right)

  defp map_branch_bound(subject, success, failure),
    do: add(struct_bound(subject), add({:operation_cost, :map_match}, {:max, success, failure}))

  defp guard_bound(condition, success, failure),
    do: add(struct_bound(condition), add({:operation_cost, :branch}, {:max, success, failure}))

  defp struct_binary_bound(operation, left, right),
    do: add(struct_bound(left), add(struct_bound(right), {:operation_cost, operation}))

  defp struct_proof(expression, bound, certificates) do
    source = """
    namespace ReductionBounds.Core

    def structOriginal : Expr := #{ProofInput.expression(expression)}

    def structUpperBound (charge opaqueCost : String → Nat) : Nat :=
      #{struct_cost_source(bound)}

    theorem structCostBound (charge opaqueCost : String → Nat) (cost : Nat)
        (path : CostTree.PathCost (structOriginal.costTree charge opaqueCost) cost) :
        cost ≤ structUpperBound charge opaqueCost := by
      simpa [structOriginal, structUpperBound, Expr.costTree, CostTree.upperBound]
        using CostTree.pathCostBound path

    end ReductionBounds.Core
    """

    %Lynx.Lean{
      file: "generated_struct_bound.lean",
      span: {1, 1},
      indentation: 0,
      source: ProofInput.certificate_source(certificates) <> source
    }
  end

  defp struct_cost_source({:add, left, right}),
    do: "(#{struct_cost_source(left)} + #{struct_cost_source(right)})"

  defp struct_cost_source({:max, left, right}),
    do: "(max #{struct_cost_source(left)} #{struct_cost_source(right)})"

  defp struct_cost_source({:operation_cost, kind}),
    do: "(charge #{ProofInput.string(Atom.to_string(kind))})"

  defp struct_cost_source({:opaque_cost, id}), do: "(opaqueCost #{ProofInput.string(id)})"
  defp struct_cost_source(0), do: "0"

  @spec infer(tuple(), ReductionBounds.target(), [binary()]) :: {:ok, map()} | {:error, term()}
  def infer(core, {_, _, arity} = target, beams) do
    inputs = inputs(arity)

    case function(core, inputs, [target], beams) do
      {:ok, tree} ->
        result = %{
          target: target,
          domain: :proper_integer_list_with_integer_key_if_present,
          metric: :symbolic_cost,
          value_model: :composed,
          source: :composed,
          upper_bound: bound(tree)
        }

        {:ok, result |> Map.merge(path_bounds(tree)) |> Map.put(:program, tree)}

      :unsupported ->
        {:error, {:unsupported_list_shape, arity}}
    end
  end

  defp inputs(1), do: [{:list, "xs", :n}]
  defp inputs(2), do: [{:integer, "key"}, {:list, "xs", :n}]

  defp function({:c_fun, _, params, body}, values, stack, beams) do
    env = Map.new(Enum.zip(Enum.map(params, &:cerl.var_name/1), values))
    eval(body, env, stack, beams)
  end

  defp eval({:c_var, _, name}, env, _stack, _beams) do
    case Map.fetch(env, name) do
      {:ok, value} -> leaf(value)
      :error -> :unsupported
    end
  end

  defp eval({:c_literal, _, value}, _env, _stack, _beams), do: literal(value)

  defp eval({:c_cons, _, head, tail}, env, stack, beams) do
    chain(arguments([head, tail], env, stack, beams), fn
      [{:integer, head}, {:list, tail, size}] ->
        leaf({:list, "(#{head} :: #{tail})", add(1, size)}, {:operation_cost, :cons})

      _ ->
        :unsupported
    end)
  end

  defp eval({:c_let, _, [{:c_var, _, name}], value, body}, env, stack, beams) do
    chain(eval(value, env, stack, beams), fn value ->
      body
      |> eval(Map.put(env, name, value), stack, beams)
      |> charge({:operation_cost, :bind})
    end)
  end

  defp eval({:c_case, _, condition, clauses}, env, stack, beams) do
    with {:ok, yes, no} <- boolean_branches(condition, clauses) do
      chain(eval(condition, env, stack, beams), &eval_branch(&1, yes, no, env, stack, beams))
    end
  end

  defp eval({:c_call, _, {:c_literal, _, module}, {:c_literal, _, name}, args}, env, stack, beams)
       when is_atom(module) and is_atom(name) do
    chain(
      arguments(args, env, stack, beams),
      &call({module, name, length(args)}, &1, stack, beams)
    )
  end

  defp eval(
         {:c_apply, _, {:c_var, _, {name, arity}}, args},
         env,
         [{module, _, _} | _] = stack,
         beams
       ) do
    chain(arguments(args, env, stack, beams), &call({module, name, arity}, &1, stack, beams))
  end

  defp eval(_node, _env, _stack, _beams), do: :unsupported

  defp eval_branch({:boolean, predicate}, yes, no, env, stack, beams) do
    with {:ok, hit} <- yes |> eval(env, stack, beams) |> charge({:branch_cost, :hit}),
         {:ok, miss} <- no |> eval(env, stack, beams) |> charge({:branch_cost, :miss}) do
      {:ok, {:branch, predicate, hit, miss}}
    end
  end

  defp eval_branch(_condition, _yes, _no, _env, _stack, _beams), do: :unsupported

  defp literal(x) when is_integer(x), do: leaf({:integer, "(#{x} : Int)"})
  defp literal(x) when is_boolean(x), do: leaf({:boolean, Atom.to_string(x)})

  defp literal(xs) when is_list(xs) do
    if integer_list?(xs),
      do: leaf({:list, inspect(xs, charlists: :as_lists, limit: :infinity), length(xs)}),
      else: :unsupported
  end

  defp literal(_), do: :unsupported

  defp integer_list?([]), do: true
  defp integer_list?([head | tail]) when is_integer(head), do: integer_list?(tail)
  defp integer_list?(_), do: false

  defp arguments([], _env, _stack, _beams), do: leaf([])

  defp arguments([arg | rest], env, stack, beams) do
    chain(eval(arg, env, stack, beams), fn value ->
      chain(arguments(rest, env, stack, beams), &leaf([value | &1]))
    end)
  end

  defp call(@member, [{:integer, key}, {:list, xs, size}], _stack, _beams) do
    leaf({:boolean, "(searchHit #{key} #{xs})"}, {:builtin, @member, [key, xs], size})
  end

  defp call(@reverse, [{:list, xs, size}, {:list, acc, acc_size}], _stack, _beams) do
    leaf(
      {:list, "(List.reverse #{xs} ++ #{acc})", add(size, acc_size)},
      {:builtin, @reverse, [xs, acc], size}
    )
  end

  defp call(target, values, stack, beams) do
    with false <- target in stack or target in [@member, @reverse],
         {:ok, core} <- SearchBound.core_function(target, beams) do
      core |> function(values, [target | stack], beams) |> annotate_call(target)
    else
      _ -> :unsupported
    end
  end

  defp boolean_branches(condition, clauses) do
    clauses = :cerl_trees.map(fn node -> :cerl.set_ann(node, []) end, {:c_values, [], clauses})
    decode_branches(clauses, :cerl.set_ann(condition, []))
  end

  defp decode_branches(
         {:c_values, [],
          [
            {:c_clause, [], [{:c_literal, [], first}], {:c_literal, [], true}, left},
            {:c_clause, [], [{:c_literal, [], second}], {:c_literal, [], true}, right},
            {:c_clause, [], [{:c_var, [], _}], {:c_literal, [], true},
             {:c_primop, [], {:c_literal, [], :match_fail}, _}}
          ]},
         _condition
       )
       when is_boolean(first) and is_boolean(second) and first != second do
    if first, do: {:ok, left, right}, else: {:ok, right, left}
  end

  defp decode_branches(
         {:c_values, [],
          [
            {:c_clause, [], [{:c_var, [], pattern}], guard, no},
            {:c_clause, [], [{:c_var, [], _}], {:c_literal, [], true}, yes}
          ]},
         condition
       ) do
    if false_guard?(guard, pattern, condition), do: {:ok, yes, no}, else: :unsupported
  end

  defp decode_branches(_clauses, _condition), do: :unsupported

  defp false_guard?(
         {:c_try, [],
          {:c_let, [], [{:c_var, [], compare}],
           {:c_case, [],
            {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :"=:="},
             [{:c_var, [], tested}, {:c_literal, [], false}]},
            [
              {:c_clause, [], [{:c_literal, [], true}], {:c_literal, [], true},
               {:c_literal, [], true}},
              {:c_clause, [], [{:c_literal, [], false}], {:c_literal, [], true},
               {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :"=:="},
                [{:c_var, [], tested}, {:c_literal, [], nil}]}},
              {:c_clause, [], [{:c_var, [], _}], {:c_literal, [], true}, _}
            ]},
           {:c_call, [], {:c_literal, [], :erlang}, {:c_literal, [], :"=:="},
            [{:c_var, [], compare}, {:c_literal, [], true}]}}, [{:c_var, [], result}],
          {:c_var, [], result}, _, {:c_literal, [], false}},
         pattern,
         condition
       ),
       do: tested == pattern or condition == {:c_var, [], tested}

  defp false_guard?(_guard, _pattern, _condition), do: false

  defp leaf(value, cost \\ 0), do: {:ok, {:leaf, value, cost}}

  defp chain({:ok, {:leaf, value, cost}}, next), do: charge(next.(value), cost)

  defp chain({:ok, {:branch, condition, yes, no}}, next) do
    with {:ok, yes} <- chain({:ok, yes}, next),
         {:ok, no} <- chain({:ok, no}, next) do
      {:ok, {:branch, condition, yes, no}}
    end
  end

  defp chain(:unsupported, _next), do: :unsupported

  defp charge(tree, amount), do: map_cost(tree, &add(amount, &1))
  defp annotate_call(tree, target), do: map_cost(tree, &{:local_call, target, &1})

  defp map_cost({:ok, {:leaf, value, cost}}, annotate), do: leaf(value, annotate.(cost))

  defp map_cost({:ok, {:branch, condition, yes, no}}, annotate) do
    {:ok, yes} = map_cost({:ok, yes}, annotate)
    {:ok, no} = map_cost({:ok, no}, annotate)
    {:ok, {:branch, condition, yes, no}}
  end

  defp map_cost(:unsupported, _annotate), do: :unsupported

  defp add(0, right), do: right
  defp add(left, 0), do: left
  defp add(left, right) when is_integer(left) and is_integer(right), do: left + right
  defp add(left, right), do: {:add, left, right}

  defp bound({:leaf, _value, cost}), do: upper(cost)
  defp bound({:branch, _, yes, no}), do: {:max, bound(yes), bound(no)}

  defp path_bounds({:branch, _, yes, no}), do: %{path_bounds: %{hit: bound(yes), miss: bound(no)}}
  defp path_bounds({:leaf, _, _}), do: %{}

  defp upper({:add, left, right}), do: add(upper(left), upper(right))
  defp upper({:max, left, right}), do: {:max, upper(left), upper(right)}

  defp upper({:builtin, target, _args, size}) do
    {:ok, builtin} = ListBound.infer(target, [])
    {:call_bound, target, substitute_size(builtin.refined_upper_bound, size)}
  end

  defp upper({:local_call, target, cost}),
    do: {:call_bound, target, add({:call_cost, target}, upper(cost))}

  defp upper({:enum_reverse, xs, size}) do
    {:call_bound, {Enum, :reverse, 1},
     add({:buffer_charge, :enum_reverse}, upper({:builtin, @reverse, [xs, "[]"], size}))}
  end

  defp upper(cost), do: cost

  @spec compose_paths([{atom(), term()}]) :: map()
  def compose_paths(paths) do
    %{
      path_bounds: Map.new(paths, fn {name, cost} -> {name, upper(cost)} end),
      upper_bound: paths |> Keyword.values() |> maximum() |> upper()
    }
  end

  defp maximum([cost]), do: cost
  defp maximum([cost | rest]), do: {:max, cost, maximum(rest)}

  @spec buffer_cost_proof([{atom(), term()}]) :: String.t()
  def buffer_cost_proof(paths) do
    combined = paths |> Keyword.values() |> maximum() |> render_cost(:upper)

    primitive_proof("Reverse", @reverse) <>
      enum_reverse_proof() <>
      """
      def bufferUpperBound (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
          (n : Nat) : Nat := #{combined}

      """ <> buffer_path_proofs(paths)
  end

  defp buffer_path_proofs(paths) do
    last = length(paths) - 1

    paths
    |> Enum.with_index()
    |> Enum.map_join("\n", fn {{name, cost}, index} ->
      upper = render_cost(cost, :upper)
      member = if index == last, do: "(Nat.le_refl _)", else: "(Nat.le_max_left _ _)"

      included =
        Enum.reduce(1..index//1, member, fn _, proof ->
          "(Nat.le_trans #{proof} (Nat.le_max_right _ _))"
        end)

      """
      def #{name}Cost (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
          (a : List Int) : Nat := #{render_cost(cost, :actual)}

      theorem #{name}Bound (reverseCharge : Nat → Nat → Nat) (bufferCharge : Nat → Nat)
          (a : List Int) (n : Nat) (sizeBound : a.length ≤ n) :
          #{name}Cost reverseCharge bufferCharge a ≤ bufferUpperBound reverseCharge bufferCharge n := by
        have localBound : #{name}Cost reverseCharge bufferCharge a ≤ #{upper} :=
          #{cost_proof(cost)}
        exact Nat.le_trans localBound #{included}
      """
    end)
  end

  defp enum_reverse_proof() do
    """
    def enumReverseList : List Int → List Int
      | [] => []
      | [x] => [x]
      | [x, y] => [y, x]
      | x :: y :: z :: tail => (z :: tail).reverse ++ [y, x]

    theorem enumReverseListValue (xs : List Int) : enumReverseList xs = xs.reverse := by
      cases xs with
      | nil => rfl
      | cons x xs =>
        cases xs with
        | nil => rfl
        | cons y xs =>
          cases xs with
          | nil => rfl
          | cons z tail => simp [enumReverseList, List.reverse_cons, List.append_assoc]

    def enumReverseCost (charge : Nat → Nat → Nat) : List Int → Nat
      | x :: y :: z :: tail => (Reverse.costedReverse charge (z :: tail) [y, x]).2
      | _ => 0

    theorem enumReverseCostBound (charge : Nat → Nat → Nat) (a : List Int) (n : Nat)
        (sizeBound : a.length ≤ n) :
        enumReverseCost charge a ≤ Reverse.listRefinedUpperBound charge n := by
      cases a with
      | nil => exact Nat.zero_le _
      | cons x a =>
        cases a with
        | nil => exact Nat.zero_le _
        | cons y a =>
          cases a with
          | nil => exact Nat.zero_le _
          | cons z tail =>
            exact (Reverse.listValueAndBound charge (z :: tail) [y, x] n (by
              simp only [List.length_cons] at sizeBound ⊢
              omega)).2.2

    """
  end

  defp substitute_size(:n, size), do: size

  defp substitute_size(expr, size) when is_tuple(expr) do
    expr |> Tuple.to_list() |> Enum.map(&substitute_size(&1, size)) |> List.to_tuple()
  end

  defp substitute_size(expr, _size), do: expr

  @spec proof(map()) :: Lynx.Lean.t()
  def proof(%{target: target, program: tree}) do
    %Lynx.Lean{
      file: "generated_composed_bound.lean",
      span: {1, 1},
      indentation: 0,
      source:
        primitive_proof("Member", @member) <>
          primitive_proof("Reverse", @reverse) <>
          primitive_lemmas() <>
          program_proof(target, tree)
    }
  end

  defp primitive_proof(namespace, target) do
    {:ok, candidate} = ListBound.infer(target, [])
    "namespace #{namespace}\n" <> ListBound.proof(candidate).source <> "\nend #{namespace}\n\n"
  end

  defp primitive_lemmas() do
    """
    def searchHit (key : Int) : List Int → Bool
      | [] => false
      | head :: tail => if head = key then true else searchHit key tail

    def boolTerm (b : Bool) : Lynx.Term := .atom (if b then "true" else "false")

    theorem searchValue (charge : Nat → Nat → Nat) (key : Int) (xs : List Int) :
        (Member.costedSearch charge key xs).1 = boolTerm (searchHit key xs) := by
      induction xs with
      | nil => rfl
      | cons head tail ih =>
        by_cases equal : head = key <;> simp [searchHit, Member.costedSearch, equal, ih, boolTerm]

    theorem memberValue (key : Int) (xs : List Int) :
        Erlang.lists.«member/2» (.integer key) (Member.integerListTerm xs) =
          .ok (boolTerm (searchHit key xs)) := by
      rw [← searchValue (fun _ _ => 0)]
      exact Member.listValueAgreement (fun _ _ => 0) key xs

    theorem encodingsAgree (xs : List Int) :
        Reverse.integerListTerm xs = Member.integerListTerm xs := by
      induction xs with
      | nil => rfl
      | cons head tail ih => simp [Reverse.integerListTerm, Member.integerListTerm, ih]

    theorem listTermNil : Lynx.Term.nil = Member.integerListTerm [] := rfl

    theorem listTermCons (head : Int) (tail : List Int) :
        Lynx.Term.cons (.integer head) (Member.integerListTerm tail) =
          Member.integerListTerm (head :: tail) := rfl

    theorem reverseValue (xs acc : List Int) :
        Erlang.lists.«reverse/2» (Member.integerListTerm xs) (Member.integerListTerm acc) =
          .ok (Member.integerListTerm (xs.reverse ++ acc)) := by
      simpa only [encodingsAgree] using
        (Reverse.listValueAndBound (fun _ _ => 0) xs acc xs.length (Nat.le_refl _)).1

    """
  end

  @charges "(memberCharge reverseCharge : Nat → Nat → Nat) (opCharge : Nat → Nat) (hitCharge missCharge localCharge : Nat)"
  @charge_args "memberCharge reverseCharge opCharge hitCharge missCharge localCharge"

  defp program_proof({_, _, arity} = target, tree) do
    {binders, args, terms} = lean_inputs(arity)
    function = "#{lean_name(target)} #{terms}"

    rules = [
      lean_name(target) <> ".eq_def"
      | Enum.map(local_targets(tree), &(lean_name(&1) <> ".eq_def"))
    ]

    value_rules =
      Enum.join(
        rules ++
          [
            "memberValue",
            "reverseValue",
            "boolTerm",
            "listTermNil",
            "listTermCons",
            "Lynx.Term.list",
            "Lynx.Except.guard",
            "Lynx.Term.isMember",
            "Except.bind",
            "pure",
            "Except.pure"
          ],
        ", "
      )

    """
    def programValue #{binders} : Lynx.Term :=
      #{render_tree(tree, fn value, _ -> encode(value) end)}

    def programCost #{@charges} #{binders} : Nat :=
      #{render_tree(tree, fn _, cost -> render_cost(cost, :actual) end)}

    def programPathBound #{@charges} #{binders} (n : Nat) : Nat :=
      #{render_tree(tree, fn _, cost -> render_cost(cost, :upper) end)}

    def programUpperBound #{@charges} (n : Nat) : Nat :=
      #{render_upper(tree)}

    theorem programValueAndBound #{@charges} #{binders} (n : Nat) (sizeBound : xs.length ≤ n) :
        #{function} = .ok (programValue #{args}) ∧
        programCost #{@charge_args} #{args} ≤ programPathBound #{@charge_args} #{args} n ∧
        programCost #{@charge_args} #{args} ≤ programUpperBound #{@charge_args} n := by
    #{derive(tree, value_rules, [], 1)}
    """
  end

  @spec input_bound(map()) :: String.t()
  def input_bound(%{target: {_, _, arity} = target}) do
    {binders, args, terms} = lean_inputs(arity)

    """
    theorem listInputValueAndBound #{@charges} #{binders} (precondition : inputPrecondition xs) :
        #{lean_name(target)} #{terms} = .ok (programValue #{args}) ∧
        programCost #{@charge_args} #{args} ≤ programPathBound #{@charge_args} #{args} (inputSize xs) ∧
        programCost #{@charge_args} #{args} ≤ programUpperBound #{@charge_args} (inputSize xs) :=
      programValueAndBound #{@charge_args} #{args} (inputSize xs)
        (inputLengthBound xs (inputInvariantInit xs precondition))
    """
  end

  defp lean_inputs(1), do: {"(xs : List Int)", "xs", "(Member.integerListTerm xs)"}

  defp lean_inputs(2),
    do: {"(key : Int) (xs : List Int)", "key xs", "(.integer key) (Member.integerListTerm xs)"}

  defp lean_name({module, name, arity}),
    do: "#{:lynx_core_to_leanj.module_name(module)}.«#{name}/#{arity}»"

  defp encode({:list, value, _size}), do: "(Member.integerListTerm #{value})"
  defp encode({:integer, value}), do: "(Lynx.Term.integer #{value})"
  defp encode({:boolean, value}), do: "(boolTerm #{value})"

  defp render_tree({:leaf, value, cost}, render), do: render.(value, cost)

  defp render_tree({:branch, condition, yes, no}, render) do
    "(if #{condition} then #{render_tree(yes, render)} else #{render_tree(no, render)})"
  end

  defp render_upper({:leaf, _, cost}), do: render_cost(cost, :upper)

  defp render_upper({:branch, _, yes, no}),
    do: "(max #{render_upper(yes)} #{render_upper(no)})"

  defp render_cost({:add, left, right}, mode),
    do: "(#{render_cost(left, mode)} + #{render_cost(right, mode)})"

  defp render_cost({:max, left, right}, :upper),
    do: "(max #{render_cost(left, :upper)} #{render_cost(right, :upper)})"

  defp render_cost({:buffer_charge, kind}, _mode),
    do: "(bufferCharge #{Map.fetch!(@buffer_charges, kind)})"

  defp render_cost({:enum_reverse, xs, _size}, :actual),
    do: "(bufferCharge 4 + enumReverseCost reverseCharge #{xs})"

  defp render_cost({:enum_reverse, _xs, size}, :upper),
    do: "(bufferCharge 4 + Reverse.listRefinedUpperBound reverseCharge #{render_size(size)})"

  defp render_cost({:builtin, target, _args, size}, :upper) do
    {namespace, charge} = primitive(target)
    "(#{namespace}.listRefinedUpperBound #{charge} #{render_size(size)})"
  end

  defp render_cost({:builtin, @member, [key, xs], _}, :actual),
    do: "(Member.costedSearch memberCharge #{key} #{xs}).2"

  defp render_cost({:builtin, @reverse, [xs, acc], _}, :actual),
    do: "(Reverse.costedReverse reverseCharge #{xs} #{acc}).2"

  defp render_cost({:local_call, _target, cost}, mode),
    do: "(localCharge + #{render_cost(cost, mode)})"

  defp render_cost({:branch_cost, :hit}, _mode), do: "hitCharge"
  defp render_cost({:branch_cost, :miss}, _mode), do: "missCharge"
  defp render_cost({:operation_cost, :bind}, _mode), do: "(opCharge 0)"
  defp render_cost({:operation_cost, :cons}, _mode), do: "(opCharge 1)"
  defp render_cost(:n, :upper), do: "n"
  defp render_cost(n, _mode) when is_integer(n), do: Integer.to_string(n)

  defp render_size(:n), do: "n"
  defp render_size(size), do: render_cost(size, :upper)

  defp primitive(@member), do: {"Member", "memberCharge"}
  defp primitive(@reverse), do: {"Reverse", "reverseCharge"}

  defp local_targets({:leaf, _, cost}), do: local_calls(cost)

  defp local_targets({:branch, _, yes, no}),
    do: Enum.uniq(local_targets(yes) ++ local_targets(no))

  defp local_calls({:add, left, right}), do: Enum.uniq(local_calls(left) ++ local_calls(right))
  defp local_calls({:local_call, target, cost}), do: [target | local_calls(cost)]
  defp local_calls(_cost), do: []

  defp derive({:branch, condition, yes, no}, rules, path, depth) do
    name = "branch#{depth}"
    indent = String.duplicate("  ", depth)
    no_code = derive(no, rules, [{name, :miss} | path], depth + 1)
    yes_code = derive(yes, rules, [{name, :hit} | path], depth + 1)

    "#{indent}cases #{name} : #{condition} with\n#{indent}| false =>\n#{no_code}\n#{indent}| true =>\n#{yes_code}"
  end

  defp derive({:leaf, _, cost}, rules, path, depth) do
    choices = Enum.map_join(path, "", fn {name, _} -> ", #{name}" end)
    actual = render_cost(cost, :actual)
    upper = render_cost(cost, :upper)

    """
    constructor
    · simp [programValue, #{rules}#{choices}]
    · have pathCost : #{actual} ≤ #{upper} := #{cost_proof(cost)}
      constructor
      · simpa [programCost, programPathBound#{choices}] using pathCost
      · apply Nat.le_trans (m := #{upper})
        · simpa [programCost#{choices}] using pathCost
        · unfold programUpperBound
          exact #{include_path(path)}
    """
    |> String.trim_trailing()
    |> String.split("\n")
    |> Enum.map_join("\n", &(String.duplicate("  ", depth) <> &1))
  end

  defp cost_proof({:add, left, right}),
    do: "(Nat.add_le_add #{cost_proof(left)} #{cost_proof(right)})"

  defp cost_proof({:local_call, _, cost}),
    do: "(Nat.add_le_add_left #{cost_proof(cost)} localCharge)"

  defp cost_proof({:enum_reverse, xs, :n}),
    do:
      "(Nat.add_le_add_left (enumReverseCostBound reverseCharge #{xs} n sizeBound) (bufferCharge 4))"

  defp cost_proof({:builtin, target, args, size}) do
    {namespace, charge} = primitive(target)
    xs = if target == @member, do: List.last(args), else: hd(args)
    arguments = Enum.join(args, " ")

    "((#{namespace}.listValueAndBound #{charge} #{arguments} #{render_size(size)} " <>
      "(by (try simp [List.length_append]) <;> omega : (#{xs}).length ≤ #{render_size(size)})).2.2)"
  end

  defp cost_proof(_charge), do: "(Nat.le_refl _)"

  defp include_path(path) do
    Enum.reduce(path, "(Nat.le_refl _)", fn
      {_, :hit}, acc -> "(Nat.le_trans #{acc} (Nat.le_max_left _ _))"
      {_, :miss}, acc -> "(Nat.le_trans #{acc} (Nat.le_max_right _ _))"
    end)
  end
end
