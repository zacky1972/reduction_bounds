defmodule ReductionBounds.ProtocolConditions do
  @moduledoc """
  Explicit size and event-count conditions for supplied protocol traces.

  Rules are indexed by the state before an event and its name. Every allowed
  transition needs a rule, including an empty rule for events without data.
  Required data bounds have independent finite byte and structural bounds.
  Integer conditions reuse `ReductionBounds.IntegerSize` and require a known
  magnitude bound. No encoding relationship or response-size bound is inferred
  from request data. Counts limit total occurrences over the entire trace,
  including repeated inspections and events after new arrivals.

  `check_trace/3` checks one supplied trace and returns the conditions used.
  The conditions remain assumptions for subsequent all-trace analysis; they
  are not inferred loop bounds, a cost bound, or a completion guarantee.
  Data summaries and integer values must describe the associated target data.
  That association is not proved by these model-level checks.
  """

  alias ReductionBounds.{IntegerSize, Protocol, ProtocolSize}

  defmodule Rule do
    @moduledoc "Size requirements and counters for one state/event context."
    defstruct data: [], integers: [], counts: []
    @type t :: %__MODULE__{data: [atom()], integers: [atom()], counts: [atom()]}
  end

  defmodule Observation do
    @moduledoc "Supplied data summaries and mathematical integer values for one occurrence."
    defstruct data: %{}, integers: %{}
    @type t :: %__MODULE__{data: %{atom() => ProtocolSize.t()}, integers: %{atom() => integer()}}
  end

  defstruct [:contract, data_bounds: %{}, integer_bounds: %{}, count_bounds: %{}, rules: %{}]

  @type t :: %__MODULE__{
          contract: Protocol.Contract.t(),
          data_bounds: %{atom() => ProtocolSize.t()},
          integer_bounds: %{atom() => IntegerSize.t()},
          count_bounds: %{atom() => non_neg_integer()},
          rules: %{{atom(), atom()} => Rule.t()}
        }

  @spec new(Protocol.Contract.t(), keyword()) :: {:ok, t()} | {:error, term()}
  def new(contract, options) do
    with true <- Keyword.keyword?(options),
         {:ok, options} <-
           Keyword.validate(options, [:data_bounds, :integer_bounds, :count_bounds, :rules]) do
      profile = struct!(__MODULE__, Keyword.put(options, :contract, contract))
      with :ok <- validate(profile), do: {:ok, profile}
    else
      _ -> {:error, :invalid_protocol_condition_options}
    end
  end

  @spec validate(term()) :: :ok | {:error, term()}
  def validate(%__MODULE__{} = profile) do
    with :ok <- Protocol.validate(profile.contract),
         :ok <- entries(profile.data_bounds, &ProtocolSize.known?/1, :data),
         :ok <- entries(profile.integer_bounds, &integer_bound?/1, :integer),
         :ok <- entries(profile.count_bounds, &natural?/1, :count),
         :ok <- require_total(profile.count_bounds),
         :ok <- rule_coverage(profile) do
      validate_rules(profile)
    end
  end

  def validate(value), do: {:error, {:invalid_protocol_conditions, value}}

  @doc "Measures supplied iodata fields and retains independent integer values."
  @spec observe(map(), map()) :: {:ok, Observation.t()} | {:error, term()}
  def observe(data, integers \\ %{}) do
    with true <- plain_map?(data) and plain_map?(integers),
         :ok <- entries(integers, &is_integer/1, :observed_integer),
         {:ok, summaries} <- measure_fields(data) do
      {:ok, %Observation{data: summaries, integers: integers}}
    else
      false -> {:error, :invalid_protocol_observation}
      error -> error
    end
  end

  @spec check_trace(t(), [Protocol.Event.t()], map()) :: {:ok, map()} | {:error, term()}
  def check_trace(profile, events, observations \\ %{}) do
    with :ok <- validate(profile),
         {:ok, trace} <- Protocol.check_trace(profile.contract, events),
         :ok <- observation_indexes(observations, length(events)),
         {:ok, rows} <- checked_rows(profile, trace, observations),
         {:ok, counts} <- checked_counts(profile, rows) do
      {:ok,
       %{
         source: :protocol_conditions,
         trace: trace,
         conditions: profile,
         rows: rows,
         counts: counts,
         lean_status: :not_checked,
         assumptions: [:size_summary_association, :integer_value_association],
         unverified: [
           :all_trace_count_bounds,
           :cost_bound,
           :progress,
           :source_correspondence,
           :runtime_correspondence
         ]
       }}
    end
  end

  defp entries(values, predicate, kind) do
    if plain_map?(values),
      do: valid_entries(values, predicate, kind),
      else: {:error, {:invalid_protocol_condition_map, kind, values}}
  end

  defp valid_entries(values, predicate, kind) do
    case Enum.find(values, fn {key, value} -> not (name?(key) and predicate.(value)) end) do
      nil -> :ok
      entry -> {:error, {:invalid_protocol_condition, kind, entry}}
    end
  end

  defp integer_bound?(value) do
    IntegerSize.valid?(value) and
      match?(%IntegerSize{magnitude_bits: bits} when is_integer(bits), value) and
      IntegerSize.normalize(value) != :unreachable
  end

  defp require_total(counts) do
    if Map.has_key?(counts, :total_events),
      do: :ok,
      else: {:error, {:missing_protocol_condition, :count, :total_events}}
  end

  defp rule_coverage(profile) do
    expected = Enum.map(profile.contract.transitions, fn {state, name, _} -> {state, name} end)

    if plain_map?(profile.rules) and Enum.sort(Map.keys(profile.rules)) == Enum.sort(expected),
      do: :ok,
      else: {:error, :protocol_condition_rule_coverage}
  end

  defp validate_rules(profile) do
    Enum.reduce_while(profile.rules, :ok, fn {context, rule}, :ok ->
      case validate_rule(rule, profile) do
        :ok -> {:cont, :ok}
        {:error, reason} -> {:halt, {:error, {:invalid_protocol_condition_rule, context, reason}}}
      end
    end)
  end

  defp validate_rule(%Rule{} = rule, profile) do
    with :ok <- references(rule.data, profile.data_bounds, :data),
         :ok <- references(rule.integers, profile.integer_bounds, :integer),
         :ok <- references(rule.counts, profile.count_bounds, :count) do
      if :total_events in rule.counts,
        do: {:error, :total_events_is_implicit},
        else: :ok
    end
  end

  defp validate_rule(value, _profile), do: {:error, {:invalid_rule, value}}

  defp references(names, bounds, kind) do
    if unique_names?(names),
      do: missing_reference(names, bounds, kind),
      else: {:error, {:invalid_condition_names, kind, names}}
  end

  defp missing_reference(names, bounds, kind) do
    case Enum.find(names, &(not Map.has_key?(bounds, &1))) do
      nil -> :ok
      name -> {:error, {:missing_protocol_condition, kind, name}}
    end
  end

  defp measure_fields(data) do
    Enum.reduce_while(data, {:ok, %{}}, fn {name, value}, {:ok, result} ->
      measure_field(name, value, result)
    end)
  end

  defp measure_field(name, value, result) do
    if name?(name),
      do: add_summary(name, value, result),
      else: {:halt, {:error, {:invalid_data_name, name}}}
  end

  defp add_summary(name, value, result) do
    case ProtocolSize.from_iodata(value) do
      {:ok, summary} -> {:cont, {:ok, Map.put(result, name, summary)}}
      {:error, reason} -> {:halt, {:error, {:protocol_data, name, reason}}}
    end
  end

  defp observation_indexes(values, length) when is_map(values) and not is_struct(values) do
    case Enum.find(values, fn {index, _} -> not (natural?(index) and index < length) end) do
      nil -> :ok
      entry -> {:error, {:invalid_observation_index, entry}}
    end
  end

  defp observation_indexes(value, _length), do: {:error, {:invalid_protocol_observations, value}}

  defp checked_rows(profile, trace, observations) do
    trace.states
    |> Enum.drop(-1)
    |> Enum.zip(trace.events)
    |> Enum.with_index()
    |> Enum.reduce_while({:ok, []}, fn {{state, event}, index}, {:ok, rows} ->
      check_row(profile, state, event, index, Map.get(observations, index, %Observation{}), rows)
    end)
    |> ordered_rows()
  end

  defp ordered_rows({:ok, rows}), do: {:ok, Enum.reverse(rows)}
  defp ordered_rows(error), do: error

  defp check_row(profile, state, event, index, observation, rows) do
    rule = Map.fetch!(profile.rules, {state, event.name})

    case check_observation(profile, rule, observation) do
      :ok ->
        {:cont,
         {:ok,
          [
            %{state: state, event: event.name, index: index, rule: rule, observation: observation}
            | rows
          ]}}

      {:error, reason} ->
        {:halt, {:error, {:protocol_condition_failed, index, state, event.name, reason}}}
    end
  end

  defp check_observation(profile, rule, %Observation{} = observation) do
    with :ok <- entries(observation.data, &ProtocolSize.known?/1, :observed_data),
         :ok <- entries(observation.integers, &is_integer/1, :observed_integer),
         :ok <- check_data(profile, rule.data, observation.data) do
      check_integers(profile, rule.integers, observation.integers)
    end
  end

  defp check_observation(_profile, _rule, value),
    do: {:error, {:invalid_protocol_observation, value}}

  defp check_data(profile, names, data) do
    Enum.reduce_while(names, :ok, fn name, :ok ->
      case Map.fetch(data, name) do
        :error -> {:halt, {:error, {:missing_data_size, name}}}
        {:ok, actual} -> data_within(name, actual, Map.fetch!(profile.data_bounds, name))
      end
    end)
  end

  defp data_within(name, actual, bound) do
    if ProtocolSize.within?(actual, bound),
      do: {:cont, :ok},
      else: {:halt, {:error, {:data_size_exceeded, name, actual, bound}}}
  end

  defp check_integers(profile, names, integers) do
    Enum.reduce_while(names, :ok, fn name, :ok ->
      case Map.fetch(integers, name) do
        :error -> {:halt, {:error, {:missing_integer_value, name}}}
        {:ok, value} -> integer_within(name, value, Map.fetch!(profile.integer_bounds, name))
      end
    end)
  end

  defp integer_within(name, value, bound) do
    if IntegerSize.contains?(bound, value),
      do: {:cont, :ok},
      else: {:halt, {:error, {:integer_condition_failed, name, value, bound}}}
  end

  defp checked_counts(profile, rows) do
    initial = Map.new(profile.count_bounds, fn {name, _bound} -> {name, 0} end)

    counts =
      Enum.reduce(rows, initial, fn row, counts ->
        Enum.reduce([:total_events | row.rule.counts], counts, &increment/2)
      end)

    case Enum.find(counts, fn {name, actual} ->
           actual > Map.fetch!(profile.count_bounds, name)
         end) do
      nil ->
        {:ok, counts}

      {name, actual} ->
        {:error, {:protocol_count_exceeded, name, actual, profile.count_bounds[name]}}
    end
  end

  defp increment(name, counts), do: Map.update!(counts, name, &(&1 + 1))

  defp unique_names?(values) do
    proper_list?(values) and Enum.all?(values, &name?/1) and
      length(values) == length(Enum.uniq(values))
  end

  defp proper_list?([]), do: true
  defp proper_list?([_head | tail]), do: proper_list?(tail)
  defp proper_list?(_value), do: false
  defp plain_map?(value), do: is_map(value) and not is_struct(value)
  defp natural?(value), do: is_integer(value) and value >= 0
  defp name?(value), do: is_atom(value) and value not in [nil, true, false]
end
