defmodule ReductionBounds.RpcTerm do
  @moduledoc """
  A bounded message grammar distinct from Port iodata measures.

  Reified terms are `{:atom, string}`, `{:integer, integer}`, `{:binary, binary}`,
  `{:ref | :pid, natural}`, `:nil`, `{:cons, head, tail}`, and tuples with the
  tags `:tuple2`, `:tuple3`, `:tuple5`. References/PIDs are abstract identities,
  not actual runtime values or evidence of freshness. Atoms are opaque symbols.
  Measures count tree nodes, total binary bytes and maximum integer magnitude
  bits independently; they do not describe ERTS representation or encoded size.
  """

  alias ReductionBounds.{IntegerSize, ProofInput}

  defmodule Size do
    @moduledoc "Independent finite message dimensions; unknown is not zero."
    defstruct nodes: :unknown, bytes: :unknown, integer_bits: :unknown

    @type t :: %__MODULE__{
            nodes: non_neg_integer() | :unknown,
            bytes: non_neg_integer() | :unknown,
            integer_bits: non_neg_integer() | :unknown
          }
  end

  @type t :: nil | tuple()

  @spec known?(term()) :: boolean()
  def known?(%Size{} = size),
    do: Enum.all?([size.nodes, size.bytes, size.integer_bits], &natural?/1)

  def known?(_value), do: false

  @spec measure(term()) :: {:ok, Size.t()} | {:error, term()}
  def measure(term) do
    case parts(term) do
      {:leaf, size} ->
        {:ok, size}

      {:children, children} ->
        measure_children(children, %Size{nodes: 1, bytes: 0, integer_bits: 0})

      :error ->
        {:error, {:unsupported_rpc_term, term}}
    end
  end

  @spec within?(Size.t(), Size.t()) :: boolean()
  def within?(actual, cap),
    do:
      known?(actual) and known?(cap) and actual.nodes <= cap.nodes and actual.bytes <= cap.bytes and
        actual.integer_bits <= cap.integer_bits

  @doc "Reifies supported actual data, rejecting actual references/PIDs and unsupported types."
  @spec from_term(term()) :: {:ok, t()} | {:error, term()}
  def from_term(value) when is_atom(value), do: {:ok, {:atom, Atom.to_string(value)}}
  def from_term(value) when is_integer(value), do: {:ok, {:integer, value}}
  def from_term(value) when is_binary(value), do: {:ok, {:binary, value}}
  def from_term([]), do: {:ok, nil}

  def from_term([head | tail]) do
    with {:ok, h} <- from_term(head), {:ok, t} <- from_term(tail), do: {:ok, {:cons, h, t}}
  end

  def from_term(value) when is_tuple(value) and tuple_size(value) in [2, 3, 5] do
    with {:ok, children} <- reify(Tuple.to_list(value)),
         do: {:ok, List.to_tuple([tuple_tag(tuple_size(value)) | children])}
  end

  def from_term(value), do: {:error, {:unsupported_rpc_value, value}}

  @doc false
  @spec lean(t()) :: String.t()
  def lean(nil), do: ".nil"
  def lean({:atom, value}), do: "(.atom #{ProofInput.string(value)})"
  def lean({:integer, value}), do: "(.integer (#{value}))"
  def lean({:binary, value}), do: "(.binary [#{Enum.join(:binary.bin_to_list(value), ", ")}])"
  def lean({kind, value}) when kind in [:ref, :pid], do: "(.#{kind} #{value})"

  def lean(value) do
    [kind | children] = Tuple.to_list(value)
    "(.#{kind} #{Enum.map_join(children, " ", &lean/1)})"
  end

  @doc false
  @spec lean_size(Size.t()) :: String.t()
  def lean_size(size), do: "⟨#{size.nodes}, #{size.bytes}, #{size.integer_bits}⟩"

  defp parts(nil), do: leaf()
  defp parts({:atom, v}) when is_binary(v), do: if(String.valid?(v), do: leaf(), else: :error)

  defp parts({:integer, v}) when is_integer(v),
    do:
      {:leaf, %Size{nodes: 1, bytes: 0, integer_bits: IntegerSize.from_integer(v).magnitude_bits}}

  defp parts({:binary, v}) when is_binary(v),
    do: {:leaf, %Size{nodes: 1, bytes: byte_size(v), integer_bits: 0}}

  defp parts({k, v}) when k in [:ref, :pid] and is_integer(v) and v >= 0, do: leaf()
  defp parts({k, a, b}) when k in [:cons, :tuple2], do: {:children, [a, b]}
  defp parts({:tuple3, a, b, c}), do: {:children, [a, b, c]}
  defp parts({:tuple5, a, b, c, d, e}), do: {:children, [a, b, c, d, e]}
  defp parts(_term), do: :error
  defp leaf(), do: {:leaf, %Size{nodes: 1, bytes: 0, integer_bits: 0}}
  defp natural?(v), do: is_integer(v) and v >= 0
  defp measure_children([], size), do: {:ok, size}

  defp measure_children([term | rest], size) do
    with {:ok, next} <- measure(term) do
      measure_children(rest, %Size{
        nodes: size.nodes + next.nodes,
        bytes: size.bytes + next.bytes,
        integer_bits: max(size.integer_bits, next.integer_bits)
      })
    end
  end

  defp reify([]), do: {:ok, []}

  defp reify([value | rest]) do
    with {:ok, value} <- from_term(value), {:ok, rest} <- reify(rest), do: {:ok, [value | rest]}
  end

  defp tuple_tag(2), do: :tuple2
  defp tuple_tag(3), do: :tuple3
  defp tuple_tag(5), do: :tuple5
end
