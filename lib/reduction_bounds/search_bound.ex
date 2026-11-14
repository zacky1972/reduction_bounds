defmodule ReductionBounds.SearchBound do
  @moduledoc false
  # cspell:words cerl primop simpa succ

  @spec infer(term(), [binary()]) :: {:ok, map()} | {:error, term()}
  def infer({module, name, 2} = target, beams) when is_atom(module) and is_atom(name) do
    with {:ok, beam} <- find_beam(module, beams),
         {:ok, core} <- read_core(module, beam),
         :ok <- recognize(core, name) do
      {:ok, candidate(target)}
    end
  end

  def infer(target, _beams), do: {:error, {:unsupported_target, target}}

  defp find_beam(module, beams) do
    case Enum.find(Enum.reverse(beams), &(beam_module(&1) == module)) do
      nil ->
        case :code.which(module) do
          [_ | _] = path -> {:ok, path}
          _ -> {:error, {:beam_not_found, module}}
        end

      beam ->
        {:ok, beam}
    end
  end

  defp beam_module(beam) do
    case :beam_lib.info(beam) do
      info when is_list(info) -> Keyword.get(info, :module)
      _ -> nil
    end
  end

  defp read_core(module, beam) do
    with {:ok, {^module, [debug_info: {:debug_info_v1, backend, data}]}} <-
           :beam_lib.chunks(beam, [:debug_info]),
         {:ok, core} <- backend.debug_info(:core_v1, module, data, []) do
      {:ok, core}
    else
      reason -> {:error, {:core_unavailable, module, reason}}
    end
  end

  defp recognize(core, name) do
    case Enum.find(:cerl.module_defs(core), fn {var, _body} ->
           :cerl.var_name(var) == {name, 2}
         end) do
      nil -> {:error, {:function_not_found, name, 2}}
      {_var, body} -> recognize_body(body, name)
    end
  end

  defp recognize_body(
         {:c_fun, _, [{:c_var, _, key}, {:c_var, _, list}],
          {:c_case, _, {:c_values, _, [{:c_var, _, key}, {:c_var, _, list}]},
           [empty, hit, step, {:c_clause, [:compiler_generated], _, _, fallback}]}},
         name
       ) do
    if empty_clause?(empty) and hit_clause?(hit) and step_clause?(step, name) and
         match?({:c_primop, _, {:c_literal, _, :match_fail}, _}, fallback) do
      :ok
    else
      {:error, :unsupported_search_shape}
    end
  end

  defp recognize_body(_body, _name), do: {:error, :unsupported_search_shape}

  defp empty_clause?(
         {:c_clause, _, [{:c_var, _, _}, {:c_literal, _, []}], {:c_literal, _, true},
          {:c_literal, _, false}}
       ),
       do: true

  defp empty_clause?(_clause), do: false

  defp hit_clause?(
         {:c_clause, _, [{:c_var, _, key}, {:c_cons, _, {:c_var, _, head}, {:c_var, _, tail}}],
          {:c_call, _, {:c_literal, _, :erlang}, {:c_literal, _, :"=:="},
           [{:c_var, _, left}, {:c_var, _, right}]}, {:c_literal, _, true}}
       ) do
    distinct?(key, head, tail) and
      ((left == key and right == head) or (left == head and right == key))
  end

  defp hit_clause?(_clause), do: false

  defp step_clause?(
         {:c_clause, _, [{:c_var, _, key}, {:c_cons, _, {:c_var, _, head}, {:c_var, _, tail}}],
          {:c_literal, _, true},
          {:c_apply, _, {:c_var, _, {name, 2}}, [{:c_var, _, key}, {:c_var, _, tail}]}},
         name
       ),
       do: distinct?(key, head, tail)

  defp step_clause?(_clause, _name), do: false

  defp distinct?(a, b, c), do: a != b and a != c and b != c

  defp candidate(target) do
    %{
      target: target,
      domain: :integer_key_and_proper_integer_list,
      metric: :symbolic_cost,
      recurrence: %{empty: :c_empty, hit: :c_hit, miss: {:add, :c_step, {:cost, :tail}}},
      upper_bound: {:add, {:max, :c_empty, :c_hit}, {:mul, :n, :c_step}}
    }
  end

  @spec proof() :: Lynx.Lean.t()
  def proof() do
    %Lynx.Lean{
      file: "generated_search_bound.lean",
      span: {1, 1},
      indentation: 0,
      source: """
      def searchCost (empty hit step : Nat) (key : Int) : List Int → Nat
        | [] => empty
        | head :: tail => if head = key then hit else step + searchCost empty hit step key tail

      theorem searchCostBound (empty hit step : Nat) (key : Int) (xs : List Int) (n : Nat)
          (sizeBound : xs.length ≤ n) :
          searchCost empty hit step key xs ≤ max empty hit + n * step := by
        have exactLength (ys : List Int) :
            searchCost empty hit step key ys ≤ max empty hit + ys.length * step := by
          induction ys with
          | nil =>
              simpa [searchCost] using (Nat.le_max_left empty hit)
          | cons head tail ih =>
              by_cases equal : head = key
              · simp only [searchCost, if_pos equal]
                exact Nat.le_trans (Nat.le_max_right empty hit) (Nat.le_add_right _ _)
              · simp only [searchCost, if_neg equal, List.length_cons, Nat.succ_mul]
                omega
        exact Nat.le_trans (exactLength xs)
          (Nat.add_le_add_left (Nat.mul_le_mul_right step sizeBound) _)
      """
    }
  end
end
