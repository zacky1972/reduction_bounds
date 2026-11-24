defmodule ReductionBounds.Mailbox do
  @moduledoc """
  Executable ordinary-message selective receive, with finite supplied conditions.

  `:begin_receive` restarts at the oldest retained message. `:inspect` tests the
  next message against ordered clauses and guards, retaining misses. Arrivals
  append; a suspended receive resumes at its cursor. `:timeout` is an observation
  allowed only for a finite timeout after all present messages were rejected.
  Its numeric value is not a cost or elapsed-time guarantee. Selection removes
  only the first eligible message. Post-return arrivals remain in the queue.

  Conditions bound all initial/arriving messages, including unrelated messages,
  and total counters across repeated receives. No receive optimization or
  inference from initial queue length is used. Checks remain supplied-model
  evidence, not source correspondence or a cost/progress theorem.
  """
  alias ReductionBounds.{MailboxMatch, RpcTerm}

  @counters [:steps, :arrivals, :receives, :inspections, :pattern_attempts, :guard_attempts]
  @type spec :: %{
          clauses: list(),
          message_size: RpcTerm.Size.t(),
          limits: map(),
          timeout: non_neg_integer() | :infinity
        }
  @type state :: map()

  @spec counters() :: [atom()]
  def counters(), do: @counters
  @spec zero() :: map()
  def zero(), do: Map.new(@counters, &{&1, 0})

  @spec new(keyword()) :: {:ok, spec()} | {:error, term()}
  def new(options) do
    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, [:clauses, :message_size, :limits, :timeout]),
         spec = Map.new(options),
         :ok <- validate(spec) do
      {:ok, spec}
    else
      false -> {:error, :invalid_mailbox_options}
      error -> error
    end
  end

  @spec validate(term()) :: :ok | {:error, term()}
  def validate(%{clauses: clauses, message_size: size, limits: limits, timeout: timeout} = spec) do
    cond do
      map_size(spec) != 4 ->
        {:error, :invalid_mailbox_spec}

      not RpcTerm.known?(size) ->
        {:error, {:missing_mailbox_condition, :message_size}}

      not (timeout == :infinity or natural?(timeout)) ->
        {:error, :invalid_mailbox_timeout}

      true ->
        with :ok <- valid_limits(limits), do: MailboxMatch.validate(clauses)
    end
  end

  def validate(_spec), do: {:error, :invalid_mailbox_spec}

  @spec initial(spec(), list()) :: {:ok, state()} | {:error, term()}
  def initial(spec, queue) do
    with :ok <- validate(spec), :ok <- messages(spec, queue) do
      {:ok, %{queue: queue, cursor: 0, phase: :idle, selected: nil, clause: nil}}
    end
  end

  @spec run(spec(), list(), list()) :: {:ok, map()} | {:error, term()}
  def run(spec, queue, actions) do
    with {:ok, state} <- initial(spec, queue),
         {:ok, state, counts} <- walk(spec, actions, state, zero(), 0) do
      {:ok,
       %{
         state: state,
         counts: counts,
         spec: spec,
         initial: queue,
         actions: actions,
         lean_status: :not_checked,
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

  @spec step(spec(), state(), term()) :: {:ok, state(), map()} | {:error, term()}
  def step(spec, state, {:arrive, term}) do
    with :ok <- messages(spec, [term]),
         do: {:ok, %{state | queue: state.queue ++ [term]}, delta(arrivals: 1)}
  end

  def step(_spec, state, :begin_receive) when state.phase in [:idle, :selected, :timed_out],
    do:
      {:ok, %{state | cursor: 0, phase: :searching, selected: nil, clause: nil},
       delta(receives: 1)}

  def step(spec, %{phase: :searching} = state, :inspect) do
    case Enum.fetch(state.queue, state.cursor) do
      {:ok, term} -> inspect_message(spec, state, term)
      :error -> {:error, :no_pending_message}
    end
  end

  def step(spec, %{phase: :searching} = state, :timeout) do
    if spec.timeout != :infinity and state.cursor == length(state.queue) and
         rejected_prefix?(spec, state),
       do: {:ok, %{state | phase: :timed_out, cursor: 0}, delta([])},
       else: {:error, :timeout_requires_exhausted_search}
  end

  def step(_spec, _state, action), do: {:error, {:invalid_mailbox_action, action}}

  @spec add(map(), map()) :: map()
  def add(a, b), do: Map.new(@counters, &{&1, a[&1] + b[&1]})
  @spec counts_within?(map(), map()) :: boolean()
  def counts_within?(counts, limits), do: Enum.all?(@counters, &(counts[&1] <= limits[&1]))

  defp walk(_spec, [], state, counts, _index), do: {:ok, state, counts}

  defp walk(spec, [action | rest], state, counts, index) do
    with {:ok, next, delta} <- step(spec, state, action),
         total = add(counts, delta),
         true <- counts_within?(total, spec.limits) do
      walk(spec, rest, next, total, index + 1)
    else
      false -> {:error, {:mailbox_step, index, :count_limit_exceeded}}
      {:error, reason} -> {:error, {:mailbox_step, index, reason}}
    end
  end

  defp walk(_spec, _actions, _state, _counts, _index), do: {:error, :invalid_mailbox_actions}

  defp inspect_message(spec, state, term) do
    {clause, patterns, guards} = MailboxMatch.choose(spec.clauses, term)
    delta = delta(inspections: 1, pattern_attempts: patterns, guard_attempts: guards)

    if rejected_prefix?(spec, state) do
      next =
        if is_nil(clause),
          do: %{state | cursor: state.cursor + 1},
          else: %{
            state
            | queue: List.delete_at(state.queue, state.cursor),
              cursor: 0,
              phase: :selected,
              selected: term,
              clause: clause
          }

      {:ok, next, delta}
    else
      {:error, :earlier_matching_message}
    end
  end

  # A certificate side condition, not additional modeled inspections/attempts.
  defp rejected_prefix?(spec, state),
    do:
      Enum.all?(
        Enum.take(state.queue, state.cursor),
        &(elem(MailboxMatch.choose(spec.clauses, &1), 0) == nil)
      )

  defp delta(values), do: zero() |> Map.merge(Map.new(values)) |> Map.put(:steps, 1)

  defp messages(_spec, []), do: :ok

  defp messages(spec, [term | rest]) do
    with {:ok, size} <- RpcTerm.measure(term), true <- RpcTerm.within?(size, spec.message_size) do
      messages(spec, rest)
    else
      false -> {:error, {:message_size_exceeded, term}}
      error -> error
    end
  end

  defp messages(_spec, _terms), do: {:error, :invalid_mailbox_messages}

  defp valid_limits(limits) when is_map(limits) and not is_struct(limits) do
    cond do
      Enum.sort(Map.keys(limits)) != Enum.sort(@counters) ->
        {:error, {:missing_mailbox_conditions, @counters -- Map.keys(limits)}}

      not Enum.all?(Map.values(limits), &natural?/1) ->
        {:error, :invalid_mailbox_limits}

      true ->
        :ok
    end
  end

  defp valid_limits(_limits), do: {:error, :invalid_mailbox_limits}
  defp natural?(v), do: is_integer(v) and v >= 0
end
