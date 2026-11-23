defmodule ReductionBounds.ProtocolCost do
  @moduledoc """
  Symbolic participant budgets for finite protocol traces and their prefixes.

  Each owned state/event context supplies a nonnegative expression and a
  counter that counts that context. Expressions accept natural constants,
  `{:charge, name}`, `{:data, slot, :bytes | :structure}`,
  `{:integer, slot, :magnitude_bits}`, and `{:add | :mul | :max, left, right}`.
  Size references must be required by the context's condition rule.

  Contexts assigned to the same participant and counter share the maximum
  local budget. The participant budget adds these maxima multiplied by the
  corresponding count limits. Charge names are scoped to each participant.
  Participants without modeled work events receive no budget claim.

  `new/2` and `check_trace/3` validate evidence in Elixir. Use
  the protocol cost proof builder and the packaged Lean sources to check the
  universal safety theorems (see the proof notes and proof test). No completion, source-code, runtime
  reduction, or elapsed-time guarantee follows from these symbolic budgets.
  """

  alias ReductionBounds.{ProtocolConditions, ProtocolSize}

  defstruct [:conditions, :rules, :groups, :bounds, :unmodeled_participants]

  @type t :: %__MODULE__{
          conditions: ProtocolConditions.t(),
          rules: map(),
          groups: [map()],
          bounds: map(),
          unmodeled_participants: [atom()]
        }

  @spec new(ProtocolConditions.t(), map()) :: {:ok, t()} | {:error, term()}
  def new(conditions, rules) when is_map(rules) do
    with :ok <- ProtocolConditions.validate(conditions),
         :ok <- validate_rules(conditions, rules) do
      groups = groups(conditions, rules)
      bounds = bounds(conditions, groups)

      {:ok,
       %__MODULE__{
         conditions: conditions,
         rules: rules,
         groups: groups,
         bounds: bounds,
         unmodeled_participants: Map.keys(conditions.contract.participants) -- Map.keys(bounds)
       }}
    end
  end

  def new(_conditions, rules), do: {:error, {:invalid_cost_rules, rules}}

  @spec check_trace(t(), list(), map()) :: {:ok, map()} | {:error, term()}
  def check_trace(profile, events, observations \\ %{})

  def check_trace(%__MODULE__{} = profile, events, observations) do
    with {:ok, canonical} <- new(profile.conditions, profile.rules),
         true <- canonical == profile,
         {:ok, result} <- ProtocolConditions.check_trace(profile.conditions, events, observations) do
      {:ok,
       Map.merge(result, %{
         source: :protocol_cost,
         cost_profile: profile,
         upper_bounds: profile.bounds,
         unmodeled_participants: profile.unmodeled_participants,
         unverified: [
           :progress,
           :source_correspondence,
           :runtime_correspondence,
           :wall_clock_time
         ],
         lean_status: :not_checked
       })}
    else
      false -> {:error, :invalid_cost_profile}
      error -> error
    end
  end

  def check_trace(_profile, _events, _observations), do: {:error, :invalid_cost_profile}

  @doc "Evaluates a closed participant budget using that participant's natural charges."
  @spec evaluate(term(), map()) :: {:ok, non_neg_integer()} | {:error, term()}
  def evaluate(expr, charges) when is_map(charges) do
    evaluate_expr(expr, charges)
  end

  def evaluate(_expr, _charges), do: {:error, :invalid_charges}

  defp evaluate_expr(value, _charges) when is_integer(value) and value >= 0, do: {:ok, value}

  defp evaluate_expr({:charge, name}, charges) do
    case Map.fetch(charges, name) do
      {:ok, value} when is_integer(value) and value >= 0 -> {:ok, value}
      _ -> {:error, {:missing_natural_charge, name}}
    end
  end

  defp evaluate_expr({operation, left, right}, charges) when operation in [:add, :mul, :max] do
    with {:ok, a} <- evaluate_expr(left, charges),
         {:ok, b} <- evaluate_expr(right, charges) do
      {:ok, arithmetic(operation, a, b)}
    end
  end

  defp evaluate_expr(expr, _charges), do: {:error, {:invalid_closed_expression, expr}}

  defp arithmetic(:add, a, b), do: a + b
  defp arithmetic(:mul, a, b), do: a * b
  defp arithmetic(:max, a, b), do: max(a, b)

  defp validate_rules(conditions, rules) do
    expected =
      for {{state, event}, _rule} <- conditions.rules,
          {owner, _unit} = Map.fetch!(conditions.contract.events, event),
          owner != nil,
          do: {state, event}

    if Enum.sort(Map.keys(rules)) == Enum.sort(expected) do
      validate_all_rules(conditions, rules)
    else
      {:error, {:cost_rule_coverage, expected, Map.keys(rules)}}
    end
  end

  defp validate_all_rules(conditions, rules) do
    Enum.reduce_while(rules, :ok, fn {context, rule}, :ok ->
      case validate_rule(conditions, context, rule) do
        :ok -> {:cont, :ok}
        error -> {:halt, error}
      end
    end)
  end

  defp validate_rule(conditions, context, %{counter: counter, cost: expr} = cost_rule)
       when map_size(cost_rule) == 2 do
    rule = Map.fetch!(conditions.rules, context)

    if (counter == :total_events or counter in rule.counts) and
         Map.has_key?(conditions.count_bounds, counter) and valid_expr?(expr, rule) do
      :ok
    else
      {:error, {:invalid_cost_rule, context, cost_rule}}
    end
  end

  defp validate_rule(_conditions, context, rule),
    do: {:error, {:invalid_cost_rule, context, rule}}

  defp valid_expr?(n, _rule) when is_integer(n) and n >= 0, do: true
  defp valid_expr?({:charge, name}, _rule), do: is_atom(name) and name != nil

  defp valid_expr?({:data, slot, dimension}, rule),
    do: slot in rule.data and dimension in [:bytes, :structure]

  defp valid_expr?({:integer, slot, :magnitude_bits}, rule), do: slot in rule.integers

  defp valid_expr?({op, left, right}, rule) when op in [:add, :mul, :max],
    do: valid_expr?(left, rule) and valid_expr?(right, rule)

  defp valid_expr?(_expr, _rule), do: false

  defp groups(conditions, rules) do
    rules
    |> Enum.sort()
    |> Enum.group_by(fn {{_state, event}, rule} ->
      {owner, _unit} = Map.fetch!(conditions.contract.events, event)
      {owner, rule.counter}
    end)
    |> Enum.sort()
    |> Enum.map(fn {{owner, counter}, entries} ->
      %{
        owner: owner,
        counter: counter,
        limit: Map.fetch!(conditions.count_bounds, counter),
        alternatives: Enum.map(entries, fn {_context, rule} -> rule.cost end)
      }
    end)
  end

  defp bounds(conditions, groups) do
    groups
    |> Enum.group_by(& &1.owner)
    |> Map.new(fn {owner, owned} ->
      {owner,
       %{
         cost_unit: Map.fetch!(conditions.contract.participants, owner),
         formula: owner_formula(conditions, owned)
       }}
    end)
  end

  defp owner_formula(conditions, groups) do
    Enum.reduce(Enum.reverse(groups), 0, fn group, rest ->
      {:add, {:mul, group.limit, maximum_formula(conditions, group.alternatives)}, rest}
    end)
  end

  defp maximum_formula(conditions, alternatives) do
    Enum.reduce(Enum.reverse(alternatives), 0, fn expr, rest ->
      {:max, cap(expr, conditions), rest}
    end)
  end

  defp cap({:data, slot, dimension}, conditions) do
    %ProtocolSize{} = size = Map.fetch!(conditions.data_bounds, slot)
    Map.fetch!(size, dimension)
  end

  defp cap({:integer, slot, :magnitude_bits}, conditions),
    do: Map.fetch!(conditions.integer_bounds, slot).magnitude_bits

  defp cap({op, left, right}, conditions) when op in [:add, :mul, :max],
    do: {op, cap(left, conditions), cap(right, conditions)}

  defp cap(expr, _conditions), do: expr
end
