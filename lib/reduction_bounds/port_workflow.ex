defmodule ReductionBounds.PortWorkflow do
  @moduledoc false

  alias ReductionBounds.{PortCompletionProof, PortProtocol, Protocol, ProtocolCost}

  @spec build(ProtocolCost.t(), list(), map(), keyword()) ::
          {:ok, map(), Lynx.Lean.t()} | {:error, term()}
  def build(profile, events, observations, completion) do
    with {:ok, _profile} <- ProtocolCost.check_trace(profile, []),
         {:ok, contract} <- PortProtocol.new(),
         {:ok, events} <- events(contract, events, 0) do
      PortCompletionProof.build(profile, events, observations, completion)
    end
  end

  defp events(_contract, [], _index), do: {:ok, []}

  defp events(contract, [head | rest], index) do
    with {:ok, event} <- event(contract, head, index),
         {:ok, rest} <- events(contract, rest, index + 1) do
      {:ok, [event | rest]}
    end
  end

  defp events(_contract, tail, index), do: {:error, {:invalid_port_event_list, index, tail}}

  defp event(contract, name, index) when is_atom(name) do
    case Protocol.event(contract, name) do
      {:ok, event} -> {:ok, event}
      {:error, reason} -> {:error, {:invalid_port_event, index, name, reason}}
    end
  end

  defp event(_contract, %Protocol.Event{} = event, _index), do: {:ok, event}
  defp event(_contract, value, index), do: {:error, {:invalid_port_event, index, value}}
end
