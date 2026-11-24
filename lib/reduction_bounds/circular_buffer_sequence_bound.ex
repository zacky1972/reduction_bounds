defmodule ReductionBounds.CircularBufferSequenceBound do
  @moduledoc false
  # cspell:words cerl primop

  alias ReductionBounds.{CircularBufferBound, CoreFragment, PeriodicBound, SearchBound}

  @initializer {CircularBuffer, :new, 1}

  @spec infer([binary()]) :: {:ok, map()} | {:error, term()}
  def infer(beams) do
    with {:ok, single} <- CircularBufferBound.infer(beams, :m),
         {:ok, core} <- SearchBound.core_function(@initializer, beams),
         true <- empty_initializer?(core) do
      {:ok, sequence_candidate(single)}
    else
      false -> {:error, {:unsupported_circular_buffer_shape, @initializer}}
      {:error, _} = error -> error
    end
  end

  defp sequence_candidate(%{path_bounds: paths} = single) do
    {:add, local_rotation, surcharge} = paths.rotate
    base = {:max, paths.consume, {:max, paths.fill, local_rotation}}
    rotations = {:if_zero, :m, 0, PeriodicBound.event_count(:m, 1, 1, 0, :n)}
    positive = PeriodicBound.cost_bound(base, surcharge, rotations, :n)

    single
    |> Map.drop([:path_bounds])
    |> Map.merge(%{
      domain: :integer_insertions_from_empty_circular_buffer,
      value_model: :circular_buffer_sequence_model,
      size_measure: %{m: :capacity, n: :insertions},
      periodic_rule: :constant_stride_reset,
      stride: 1,
      origin: 1,
      conditions: %{
        derived: [
          {:domain, :valid_integer_circular_buffer},
          {:initial, :empty_buffer},
          {:size_measure, :front_list_length},
          {:invariant, :valid_buffer_with_fixed_capacity},
          {:reset, :rotate_when_front_list_is_full},
          {:zero_period, :no_rotation}
        ],
        supplied: []
      },
      rotation_count: rotations,
      base_cost: base,
      rotation_surcharge: surcharge,
      upper_bound: {:if_zero, :m, {:mul, :n, paths.zero}, positive}
    })
  end

  defp empty_initializer?(
         {:c_fun, _, [{:c_var, _, input}], {:c_case, _, {:c_var, _, input}, clauses}}
       ) do
    case :cerl_trees.map(&:cerl.set_ann(&1, []), {:c_values, [], clauses}) do
      {:c_values, [],
       [
         {:c_clause, [], [{:c_var, [], size}], guard,
          {:c_map, [], {:c_literal, [], empty}, fields, false}},
         {:c_clause, [], [{:c_var, [], _}], {:c_literal, [], true},
          {:c_primop, [], {:c_literal, [], :match_fail}, _}}
       ]}
      when empty == %{} ->
        capacity_guard?(guard, input, size) and initializer_fields?(fields, size)

      _ ->
        false
    end
  end

  defp empty_initializer?(_), do: false

  defp initializer_fields?(fields, size) do
    expected = %{
      __struct__: {:c_literal, [], CircularBuffer},
      a: {:c_literal, [], []},
      b: {:c_literal, [], []},
      count: {:c_literal, [], 0},
      max_size: {:c_var, [], size}
    }

    Enum.sort(fields) ==
      Enum.sort(
        Enum.map(expected, fn {key, value} ->
          {:c_map_pair, [], {:c_literal, [], :assoc}, {:c_literal, [], key}, value}
        end)
      )
  end

  defp capacity_guard?(guard, input, size) do
    case CoreFragment.decode_guard(guard) do
      {:ok,
       {:guarded, {:is_integer, {:var, tested}}, {:ge, {:var, tested}, {:int, 0}},
        {:atom, "false"}}} ->
        Enum.any?([input, size], &(CoreFragment.variable_name({:c_var, [], &1}) == {:ok, tested}))

      _ ->
        false
    end
  end

  @spec proof() :: Lynx.Lean.t()
  def proof() do
    proof = CircularBufferBound.proof()

    %{
      proof
      | file: "generated_circular_buffer_sequence_bound.lean",
        source: ""
    }
  end
end
