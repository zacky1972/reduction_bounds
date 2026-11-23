defmodule ReductionBounds.ProtocolSize do
  @moduledoc """
  Independent byte and structural bounds for communication data.

  A structural unit is one binary, byte, empty list, or list cell. Binary
  traversal work must still use its byte bound. For example, nested empty
  lists have zero bytes but nonzero structural size. The convention is a
  mathematical measure, not a statement about ERTS traversal or allocation.

  `from_iodata/1` measures valid iodata, including binary tails. Scalar bytes
  are permitted inside lists, not as top-level iodata. Unknown information is
  explicit and is never silently interpreted as zero.

      iex> ReductionBounds.ProtocolSize.from_iodata([[], []])
      {:ok, %ReductionBounds.ProtocolSize{bytes: 0, structure: 5}}
  """

  @type dimension :: non_neg_integer() | :unknown
  @type t :: %__MODULE__{bytes: dimension(), structure: dimension()}
  defstruct bytes: :unknown, structure: :unknown

  @spec known?(term()) :: boolean()
  def known?(%__MODULE__{bytes: bytes, structure: structure}),
    do: natural?(bytes) and natural?(structure)

  def known?(_value), do: false

  @doc "Checks both dimensions; unknown information cannot establish inclusion."
  @spec within?(t(), t()) :: boolean()
  def within?(actual, bound) do
    known?(actual) and known?(bound) and actual.bytes <= bound.bytes and
      actual.structure <= bound.structure
  end

  @doc "Measures valid iodata in Elixir; association with target data remains an assumption."
  @spec from_iodata(term()) :: {:ok, t()} | {:error, term()}
  def from_iodata(data) do
    with {:ok, bytes, nodes} <- container(data) do
      {:ok, %__MODULE__{bytes: bytes, structure: nodes}}
    end
  end

  defp container(data) when is_binary(data), do: {:ok, byte_size(data), 1}
  defp container([]), do: {:ok, 0, 1}

  defp container([head | tail]) do
    with {:ok, bytes, nodes} <- item(head),
         {:ok, tail_bytes, tail_nodes} <- container(tail) do
      {:ok, bytes + tail_bytes, 1 + nodes + tail_nodes}
    end
  end

  defp container(value), do: {:error, {:invalid_iodata, value}}
  defp item(byte) when is_integer(byte) and byte in 0..255, do: {:ok, 1, 1}
  defp item(value), do: container(value)
  defp natural?(value), do: is_integer(value) and value >= 0
end
