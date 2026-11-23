defmodule ReductionBounds.Protocol do
  @moduledoc """
  Finite communication models shared by Port and request/response analyses.

  Each registered work event has exactly one owner and one cost unit. An
  environment event has neither; its occurrence describes an observation,
  not a bound on the environment's work. Participants may use different units.
  No cross-participant sum or numeric cost is computed here.

  Contracts declare states, terminal states, event metadata, and transitions.
  `check_trace/2` checks supplied model events, including unfinished prefixes.
  It does not inspect target code, prove progress, or establish runtime charges.
  Cycles permit retry and inspection traces; count bounds belong to later
  analysis. An accepted finite trace does not establish a bound for every run.

  ## Example

      iex> alias ReductionBounds.{PortProtocol, Protocol}
      iex> {:ok, contract} = PortProtocol.new()
      iex> {:ok, prepare} = Protocol.event(contract, :prepare)
      iex> {:ok, trace} = Protocol.check_trace(contract, [prepare])
      iex> {trace.final, trace.terminal?}
      {:prepared, false}
  """

  defmodule Event do
    @moduledoc "A registered model event; nil ownership and unit denote the environment."
    @enforce_keys [:name]
    defstruct [:name, :owner, :cost_unit]

    @type t :: %__MODULE__{name: atom(), owner: atom() | nil, cost_unit: atom() | nil}
  end

  defmodule Contract do
    @moduledoc "A finite, explicit protocol and its accounting declarations."
    defstruct participants: %{},
              states: [],
              initial: nil,
              terminal: [],
              events: %{},
              transitions: []

    @type t :: %__MODULE__{
            participants: %{atom() => atom()},
            states: [atom()],
            initial: atom(),
            terminal: [atom()],
            events: %{atom() => {atom() | nil, atom() | nil}},
            transitions: [{atom(), atom(), atom()}]
          }
  end

  defmodule Trace do
    @moduledoc "An Elixir-checked model trace; this struct is not Lean proof evidence."
    @enforce_keys [:contract, :events, :states, :final, :terminal?]
    defstruct [:contract, :events, :states, :final, :terminal?]

    @type t :: %__MODULE__{
            contract: Contract.t(),
            events: [Event.t()],
            states: [atom()],
            final: atom(),
            terminal?: boolean()
          }
  end

  @doc "Builds and validates a finite protocol contract."
  @spec new(keyword()) :: {:ok, Contract.t()} | {:error, term()}
  def new(options) do
    keys = [:participants, :states, :initial, :terminal, :events, :transitions]

    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, keys) do
      contract = struct!(Contract, options)
      with :ok <- validate(contract), do: {:ok, contract}
    else
      _ -> {:error, :invalid_protocol_options}
    end
  end

  @doc "Validates contracts, including directly constructed structs."
  @spec validate(term()) :: :ok | {:error, term()}
  def validate(%Contract{} = contract) do
    with :ok <- participants(contract.participants),
         :ok <- states(contract),
         :ok <- events(contract) do
      transitions(contract)
    end
  end

  def validate(value), do: {:error, {:invalid_protocol_contract, value}}

  @doc "Constructs an event with the contract's declared ownership and unit."
  @spec event(Contract.t(), atom()) :: {:ok, Event.t()} | {:error, term()}
  def event(contract, name) do
    with :ok <- validate(contract) do
      case Map.fetch(contract.events, name) do
        {:ok, {owner, unit}} -> {:ok, %Event{name: name, owner: owner, cost_unit: unit}}
        :error -> {:error, {:unknown_protocol_event, name}}
      end
    end
  end

  @doc "Checks a finite trace. Event diagnostics contain a zero-based occurrence index."
  @spec check_trace(Contract.t(), [Event.t()]) :: {:ok, Trace.t()} | {:error, term()}
  def check_trace(contract, input) do
    with :ok <- validate(contract),
         true <- proper_list?(input),
         {:ok, history} <- walk(contract, input, [contract.initial], 0) do
      [final | _] = history

      {:ok,
       %Trace{
         contract: contract,
         events: input,
         states: Enum.reverse(history),
         final: final,
         terminal?: final in contract.terminal
       }}
    else
      false -> {:error, {:invalid_protocol_events, input}}
      error -> error
    end
  end

  @doc "Selects event occurrences assigned to one participant without combining units."
  @spec events_for(Trace.t(), atom()) :: [Event.t()]
  def events_for(%Trace{events: input}, owner) when is_atom(owner) and not is_nil(owner),
    do: Enum.filter(input, &(&1.owner == owner))

  defp participants(values) when is_map(values) and not is_struct(values) do
    check(
      Enum.all?(values, fn {owner, unit} -> name?(owner) and name?(unit) end),
      {:invalid_protocol_participants, values}
    )
  end

  defp participants(values), do: {:error, {:invalid_protocol_participants, values}}

  defp states(contract) do
    with :ok <-
           check(
             unique_names?(contract.states) and contract.states != [],
             {:invalid_protocol_states, contract.states}
           ),
         :ok <-
           check(
             contract.initial in contract.states,
             {:invalid_protocol_initial, contract.initial}
           ) do
      check(
        unique_names?(contract.terminal) and
          Enum.all?(contract.terminal, &(&1 in contract.states)),
        {:invalid_protocol_terminal, contract.terminal}
      )
    end
  end

  defp events(%Contract{events: values} = contract)
       when is_map(values) and not is_struct(values) do
    case Enum.find(values, fn {name, pair} -> not (name?(name) and metadata?(pair, contract)) end) do
      nil -> :ok
      entry -> {:error, {:invalid_protocol_event, entry}}
    end
  end

  defp events(contract), do: {:error, {:invalid_protocol_events, contract.events}}

  defp metadata?({nil, nil}, _contract), do: true

  defp metadata?({owner, unit}, contract),
    do: name?(owner) and name?(unit) and Map.get(contract.participants, owner) == unit

  defp metadata?(_pair, _contract), do: false

  defp transitions(%Contract{transitions: values} = contract) do
    if proper_list?(values),
      do: validate_transitions(values, contract),
      else: {:error, {:invalid_protocol_transitions, values}}
  end

  defp validate_transitions(values, contract) do
    case Enum.find_index(values, &(not transition?(&1, contract))) do
      nil -> unique_transitions(values)
      index -> {:error, {:invalid_protocol_transition, Enum.at(values, index)}}
    end
  end

  defp transition?({from, event, to}, contract) do
    from in contract.states and to in contract.states and from not in contract.terminal and
      Map.has_key?(contract.events, event)
  end

  defp transition?(_value, _contract), do: false

  defp unique_transitions(values) do
    keys = Enum.map(values, fn {from, event, _to} -> {from, event} end)
    check(length(keys) == length(Enum.uniq(keys)), :ambiguous_protocol_transition)
  end

  defp walk(_contract, [], history, _index), do: {:ok, history}

  defp walk(contract, [event | rest], [state | _] = history, index) do
    with :ok <- matching_event(contract, event),
         {:ok, next} <- advance(contract, state, event.name) do
      walk(contract, rest, [next | history], index + 1)
    else
      {:error, reason} -> {:error, {:invalid_protocol_trace, index, event, reason}}
    end
  end

  defp matching_event(contract, %Event{} = event) do
    case Map.fetch(contract.events, event.name) do
      {:ok, {owner, unit}} ->
        check(
          {event.owner, event.cost_unit} == {owner, unit},
          {:event_metadata_mismatch, event.name, {owner, unit}}
        )

      :error ->
        {:error, {:unknown_protocol_event, event.name}}
    end
  end

  defp matching_event(_contract, value), do: {:error, {:invalid_protocol_event, value}}

  defp advance(contract, state, event) do
    case Enum.find(contract.transitions, fn {from, name, _} -> from == state and name == event end) do
      {_, _, next} -> {:ok, next}
      nil -> {:error, {:transition_not_allowed, state, event}}
    end
  end

  defp unique_names?(values) when is_list(values),
    do:
      proper_list?(values) and Enum.all?(values, &name?/1) and
        length(values) == length(Enum.uniq(values))

  defp unique_names?(_value), do: false
  defp proper_list?([]), do: true
  defp proper_list?([_head | tail]), do: proper_list?(tail)
  defp proper_list?(_value), do: false
  defp name?(value), do: is_atom(value) and value not in [nil, true, false]
  defp check(true, _reason), do: :ok
  defp check(false, reason), do: {:error, reason}
end
