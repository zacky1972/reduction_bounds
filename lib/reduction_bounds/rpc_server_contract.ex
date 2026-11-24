defmodule ReductionBounds.RpcServerContract do
  @moduledoc """
  Declares a unary integer RPC handler and its separate server frame.

  `assume/4` leaves the handler bound as an explicit assumption. `reuse/3`
  replays an integer cost derivation against current Core and instantiates its
  declarative cost contract; saved verification flags are never evidence.
  Both require `:server_work`. The frame describes the assumed server mailbox
  and reply envelope, independently of the checked client mailbox.

  Frame keys are `:message_size`, `:reply_size`, `:initial_messages`, `:arrivals`,
  `:inspections`, `:pattern_attempts`, and `:guard_attempts`. These scope the
  supplied receive/send rates; they are not checked against server execution.
  The request payload is the modeled handler argument. Connecting that
  association, the handler identity and reply encoding to source is deferred.
  """
  alias ReductionBounds.{BoundTransfer, IntegerSize, RpcTerm}

  @frame_counts [:initial_messages, :arrivals, :inspections, :pattern_attempts, :guard_attempts]

  @spec assume(tuple(), IntegerSize.t(), non_neg_integer(), map()) ::
          {:ok, map()} | {:error, term()}
  def assume(target, input, bound, frame) do
    with :ok <- target(target),
         true <- IntegerSize.valid?(input) and input != :unreachable and natural?(bound),
         :ok <- frame(frame) do
      {:ok,
       %{
         kind: :assumed,
         target: target,
         input: input,
         upper_bound: bound,
         cost_unit: :server_work,
         frame: frame
       }}
    else
      false -> {:error, :invalid_rpc_handler_contract}
      error -> error
    end
  end

  @spec reuse(map(), map(), keyword()) :: {:ok, map()} | {:error, term()}
  def reuse(bound, frame, options \\ []) do
    with true <- Keyword.keyword?(options),
         {:ok, options} <- Keyword.validate(options, [:beam_binaries, :max_unfolding, :max_nodes]),
         :ok <- frame(frame),
         :ok <- reusable(bound) do
      {:ok, %{kind: :replay, bound: bound, frame: frame, replay_options: options}}
    else
      false -> {:error, :invalid_rpc_handler_options}
      error -> error
    end
  end

  @doc false
  @spec validate(term()) :: :ok | {:error, term()}
  def validate(%{kind: :assumed, target: t, input: i, upper_bound: b, frame: f} = c) do
    case assume(t, i, b, f) do
      {:ok, ^c} -> :ok
      _ -> {:error, :invalid_rpc_handler_contract}
    end
  end

  def validate(%{kind: :replay, bound: b, frame: f, replay_options: o} = c) do
    case reuse(b, f, o) do
      {:ok, ^c} -> :ok
      _ -> {:error, :invalid_rpc_handler_contract}
    end
  end

  def validate(_contract), do: {:error, :invalid_rpc_handler_contract}

  @doc false
  @spec resolve(term(), term()) :: {:ok, map(), Lynx.Lean.t() | nil} | {:error, term()}
  def resolve(contract, {:tuple3, _, _, {:integer, value}} = request) do
    with {:ok, resolved, proof} <- replay(contract),
         {:ok, size} <- RpcTerm.measure(request),
         :ok <- request_size(size, resolved.frame.message_size),
         true <- IntegerSize.contains?(resolved.input, value) do
      {:ok, Map.put(resolved, :argument, value), proof}
    else
      false -> {:error, :rpc_handler_input_not_covered}
      error -> error
    end
  end

  def resolve(_contract, _request), do: {:error, :unsupported_rpc_handler_payload}

  defp request_size(size, cap) do
    if RpcTerm.within?(size, cap), do: :ok, else: {:error, :rpc_server_request_size_exceeded}
  end

  defp replay(%{kind: :assumed, target: t, input: i, upper_bound: b, frame: f} = c) do
    with {:ok, canonical} <- assume(t, i, b, f), true <- c == canonical do
      {:ok, Map.put(c, :status, :assumed), nil}
    else
      _ -> {:error, :invalid_rpc_handler_contract}
    end
  end

  defp replay(%{kind: :replay, bound: b, frame: f, replay_options: o} = c) do
    with {:ok, canonical} <- reuse(b, f, o),
         true <- c == canonical,
         {:ok, transferred, proof} <-
           BoundTransfer.infer(
             b,
             b.cost_contract,
             Keyword.put(o, :callee_correspondence, :shared)
           ) do
      {:ok,
       %{
         kind: :replay,
         target: b.target,
         input: hd(transferred.input_sizes),
         upper_bound: transferred.upper_bound_value,
         cost_unit: :server_work,
         frame: f,
         status: :replay_pending,
         callee_contracts: transferred.original_bound.call_contracts
       }, proof}
    else
      false -> {:error, :invalid_rpc_handler_contract}
      error -> error
    end
  end

  defp replay(_contract), do: {:error, :invalid_rpc_handler_contract}

  defp reusable(%{
         source: :integer_cost_fragment,
         target: t,
         input_sizes: [_],
         cost_contract: %{cost_unit: :server_work, functions: functions}
       })
       when is_map(functions), do: target(t)

  defp reusable(_bound), do: {:error, :rpc_handler_requires_declarative_server_work_bound}

  defp target({m, f, 1}) when is_atom(m) and is_atom(f), do: :ok
  defp target(_target), do: {:error, :rpc_handler_requires_unary_target}

  defp frame(frame) when is_map(frame) and not is_struct(frame) do
    if Enum.sort(Map.keys(frame)) == Enum.sort([:message_size, :reply_size | @frame_counts]) and
         RpcTerm.known?(frame.message_size) and RpcTerm.known?(frame.reply_size) and
         Enum.all?(@frame_counts, &natural?(frame[&1])),
       do: :ok,
       else: {:error, :invalid_rpc_server_frame}
  end

  defp frame(_frame), do: {:error, :invalid_rpc_server_frame}
  defp natural?(n), do: is_integer(n) and n >= 0
end
