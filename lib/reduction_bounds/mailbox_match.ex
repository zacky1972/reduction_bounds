defmodule ReductionBounds.MailboxMatch do
  @moduledoc """
  Ordered patterns and a restricted guard language for supplied mailbox models.

  Patterns: `:any`, `:pid`, `{:literal, reified_term}` and recursive
  `:tuple2`, `:tuple3`, `:tuple5`, `:cons` patterns. Guards: `true`, `false`,
  `{:is_integer, path}`, `{:integer_le | :integer_ge, path, bound}`.
  Paths use zero-based tuple fields or cons head/tail. No callbacks, arbitrary
  guards or native receive optimizations are assumed. Attempts count clauses,
  not machine instructions; the complete finite matching program is retained.
  """
  alias ReductionBounds.RpcTerm

  @type clause :: %{kind: :reply | :peer_down | :other, pattern: term(), guard: term()}

  @spec validate(term()) :: :ok | {:error, term()}
  def validate(clauses) when is_list(clauses) and clauses != [] do
    if proper?(clauses) and Enum.all?(clauses, &clause?/1),
      do: :ok,
      else: {:error, :invalid_mailbox_clauses}
  end

  def validate(_clauses), do: {:error, :invalid_mailbox_clauses}

  @spec choose([clause()], RpcTerm.t()) ::
          {non_neg_integer() | nil, non_neg_integer(), non_neg_integer()}
  def choose(clauses, term), do: choose(clauses, term, 0, 0)

  @spec pattern?(term()) :: boolean()
  def pattern?(:any), do: true
  def pattern?(:pid), do: true
  def pattern?({:literal, t}), do: match?({:ok, _}, RpcTerm.measure(t))

  def pattern?(p) when is_tuple(p) do
    case Tuple.to_list(p) do
      [k | children] when k in [:tuple2, :tuple3, :tuple5, :cons] ->
        tuple_size(p) == arity(k) + 1 and Enum.all?(children, &pattern?/1)

      _ ->
        false
    end
  end

  def pattern?(_p), do: false

  @spec guard?(term()) :: boolean()
  def guard?(g) when is_boolean(g), do: true
  def guard?({:is_integer, path}), do: path?(path)
  def guard?({k, path, n}) when k in [:integer_le, :integer_ge], do: path?(path) and is_integer(n)
  def guard?(_g), do: false

  @doc false
  @spec lean_pattern(term()) :: String.t()
  def lean_pattern(:any), do: ".any"
  def lean_pattern(:pid), do: ".pid"
  def lean_pattern({:literal, t}), do: "(.literal #{RpcTerm.lean(t)})"

  def lean_pattern(p) do
    [k | children] = Tuple.to_list(p)
    "(.#{k} #{Enum.map_join(children, " ", &lean_pattern/1)})"
  end

  @doc false
  @spec lean_guard(term()) :: String.t()
  def lean_guard(true), do: ".yes"
  def lean_guard(false), do: ".no"
  def lean_guard({:is_integer, path}), do: "(.isInteger [#{Enum.join(path, ", ")}])"

  def lean_guard({k, path, n}),
    do: "(.#{if(k == :integer_le, do: "le", else: "ge")} [#{Enum.join(path, ", ")}] (#{n}))"

  @spec matches?(term(), RpcTerm.t()) :: boolean()
  def matches?(:any, _term), do: true
  def matches?(:pid, {:pid, _}), do: true
  def matches?(:pid, _term), do: false
  def matches?({:literal, t}, term), do: t == term

  def matches?(p, term)
      when is_tuple(p) and is_tuple(term) and tuple_size(p) == tuple_size(term) do
    [pk | ps] = Tuple.to_list(p)
    [tk | ts] = Tuple.to_list(term)
    pk == tk and Enum.all?(Enum.zip_with(ps, ts, &matches?/2))
  end

  def matches?(_p, _term), do: false

  @spec evaluate_guard(term(), RpcTerm.t()) :: boolean()
  def evaluate_guard(g, _term) when is_boolean(g), do: g
  def evaluate_guard({:is_integer, path}, term), do: match?({:integer, _}, at_path(term, path))

  def evaluate_guard({k, path, n}, term) do
    case at_path(term, path) do
      {:integer, v} -> if(k == :integer_le, do: v <= n, else: v >= n)
      _ -> false
    end
  end

  defp choose([], _term, index, guards), do: {nil, index, guards}

  defp choose([clause | rest], term, index, guards) do
    if matches?(clause.pattern, term) do
      if evaluate_guard(clause.guard, term),
        do: {index, index + 1, guards + 1},
        else: choose(rest, term, index + 1, guards + 1)
    else
      choose(rest, term, index + 1, guards)
    end
  end

  defp clause?(%{kind: k, pattern: p, guard: g} = c),
    do: map_size(c) == 3 and k in [:reply, :peer_down, :other] and pattern?(p) and guard?(g)

  defp clause?(_c), do: false
  defp at_path(term, []), do: term

  defp at_path(term, [i | rest]) when is_tuple(term) do
    [k | children] = Tuple.to_list(term)

    if k in [:tuple2, :tuple3, :tuple5, :cons] and i < length(children),
      do: at_path(Enum.at(children, i), rest)
  end

  defp at_path(_term, _path), do: nil
  defp path?(p), do: is_list(p) and proper?(p) and Enum.all?(p, &(is_integer(&1) and &1 in 0..4))
  defp proper?([]), do: true
  defp proper?([_ | rest]), do: proper?(rest)
  defp proper?(_value), do: false
  defp arity(:tuple2), do: 2
  defp arity(:tuple3), do: 3
  defp arity(:tuple5), do: 5
  defp arity(:cons), do: 2
end
