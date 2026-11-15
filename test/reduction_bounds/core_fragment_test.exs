defmodule ReductionBounds.CoreFragmentTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.CoreFragment

  test "decodes a tagged map match and preserves the original case tail" do
    subject = var(0)
    alias_var = var(:state)
    bound = var(:balance)

    pattern =
      {:c_alias, [], alias_var,
       {:c_map, [], literal(%{}),
        [pair(:exact, :__struct__, literal(Counter)), pair(:exact, :balance, bound)], true}}

    first = {:c_clause, [], [pattern], literal(true), bound}
    later = {:c_clause, [], [var(:other)], literal(true), literal(:fallback)}
    body = {:c_case, [:source], subject, [first, later]}

    assert {:ok,
            %{
              parameters: ["integer:0"],
              expression:
                {:case_map, {:var, "integer:0"},
                 %{tag: "Elixir.Counter", fields: [{"balance", "atom:balance"}]},
                 {:let_in, "atom:state", {:var, "integer:0"}, {:var, "atom:balance"}},
                 {:opaque, id}},
              opaque: opaque
            }} = CoreFragment.decode({:c_fun, [], [subject], body})

    assert opaque == %{id => {:c_case, [:source], subject, [later]}}
  end

  test "decodes a binding, field read, and exact field update" do
    state = var(:state)
    total = var(:total)
    get = {:c_call, [], literal(:maps), literal(:get), [literal(:balance), state]}
    update = {:c_map, [], state, [pair(:exact, :balance, total)], false}

    assert {:ok,
            %{
              expression:
                {:let_in, "atom:total", {:field, {:var, "atom:state"}, "balance"},
                 {:update, {:var, "atom:state"}, "balance", {:var, "atom:total"}}},
              opaque: %{}
            }} = CoreFragment.decode({:c_fun, [], [state], {:c_let, [], [total], get, update}})
  end

  test "rejects an update that can add a key" do
    state = var(:state)
    update = {:c_map, [], state, [pair(:assoc, :balance, literal(0))], false}

    assert {:error, {:unsupported_core, ^update}} =
             CoreFragment.decode({:c_fun, [], [state], update})
  end

  test "rejects a guarded clause rather than treating its pattern as sufficient" do
    subject = var(0)
    bound = var(:balance)
    pattern = {:c_map, [], literal(%{}), [pair(:exact, :balance, bound)], true}
    guarded = {:c_clause, [], [pattern], literal(false), bound}
    body = {:c_case, [], subject, [guarded]}

    assert {:error, {:unsupported_core, ^body}} =
             CoreFragment.decode({:c_fun, [], [subject], body})
  end

  test "distinguishes integer and atom identifiers" do
    assert {:ok, %{parameters: ["integer:0", "atom:0"], expression: {:var, "atom:0"}}} =
             CoreFragment.decode({:c_fun, [], [var(0), var(:"0")], var(:"0")})
  end

  defp var(name), do: {:c_var, [], name}
  defp literal(value), do: {:c_literal, [], value}

  defp pair(operation, key, value),
    do: {:c_map_pair, [], literal(operation), literal(key), value}
end
