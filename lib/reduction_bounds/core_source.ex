defmodule ReductionBounds.CoreSource do
  @moduledoc false

  alias ReductionBounds.{CoreFragment, ProofInput}

  @spec serialize(tuple(), %{String.t() => tuple()}) :: {:ok, String.t()} | :unsupported
  def serialize({:c_fun, _, _, body}, opaque) do
    case expression(body, opaque) do
      {:ok, _source} = result -> result
      _ -> :unsupported
    end
  end

  def serialize(_core, _opaque), do: :unsupported

  defp expression({:c_var, _, _} = variable, _opaque) do
    with {:ok, name} <- CoreFragment.variable_name(variable), do: {:ok, node("var", name)}
  end

  defp expression({:c_literal, _, value}, _opaque) when is_atom(value),
    do: {:ok, node("atom", Atom.to_string(value))}

  defp expression({:c_literal, _, value}, _opaque) when is_integer(value),
    do: {:ok, "(.int (#{value}))"}

  defp expression({:c_let, _, [variable], rhs, body}, opaque) do
    with {:ok, name} <- CoreFragment.variable_name(variable),
         {:ok, rhs} <- expression(rhs, opaque),
         {:ok, body} <- expression(body, opaque) do
      {:ok, "(.letIn #{ProofInput.string(name)} #{rhs} #{body})"}
    end
  end

  defp expression(
         {:c_case, annotations, subject,
          [{:c_clause, _, [pattern], {:c_literal, _, true}, body} | rest]},
         opaque
       ) do
    with {:ok, name} <- CoreFragment.variable_name(subject),
         {:ok, alias_name, pattern} <- pattern(pattern),
         {:ok, matched} <- expression(body, opaque),
         {:ok, fallback} <- fallback({:c_case, annotations, subject, rest}, opaque) do
      subject = ProofInput.string(name)
      {:ok, "(.caseMap #{subject} #{pattern} #{optional(alias_name)} #{matched} #{fallback})"}
    end
  end

  defp expression(_body, _opaque), do: :unsupported

  defp fallback(core, opaque) do
    case Enum.find(opaque, fn {_id, source} -> source == core end) do
      {id, _source} -> {:ok, node("opaque", id)}
      nil -> :unsupported
    end
  end

  defp pattern({:c_alias, _, variable, map}) do
    with {:ok, name} <- CoreFragment.variable_name(variable),
         {:ok, pattern} <- map_pattern(map) do
      {:ok, name, pattern}
    end
  end

  defp pattern(map) do
    with {:ok, pattern} <- map_pattern(map), do: {:ok, nil, pattern}
  end

  defp map_pattern({:c_map, _, {:c_literal, _, base}, pairs, true}) when base == %{} do
    with {:ok, tag, fields} <- map_pairs(pairs, nil, []) do
      {:ok, "⟨#{optional(tag)}, [#{Enum.join(fields, ", ")}]⟩"}
    end
  end

  defp map_pattern(_map), do: :unsupported

  defp map_pairs([], tag, fields), do: {:ok, tag, Enum.reverse(fields)}

  defp map_pairs(
         [
           {:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, :__struct__},
            {:c_literal, _, tag}}
           | rest
         ],
         nil,
         fields
       )
       when is_atom(tag),
       do: map_pairs(rest, Atom.to_string(tag), fields)

  defp map_pairs(
         [
           {:c_map_pair, _, {:c_literal, _, :exact}, {:c_literal, _, key}, {:c_var, _, _} = var}
           | rest
         ],
         tag,
         fields
       )
       when is_atom(key) and key != :__struct__ do
    with {:ok, name} <- CoreFragment.variable_name(var) do
      pair = "(#{ProofInput.string(Atom.to_string(key))}, #{ProofInput.string(name)})"
      map_pairs(rest, tag, [pair | fields])
    end
  end

  defp map_pairs(_pairs, _tag, _fields), do: :unsupported

  defp optional(nil), do: "none"
  defp optional(name), do: "(some #{ProofInput.string(name)})"

  defp node(constructor, name), do: "(.#{constructor} #{ProofInput.string(name)})"
end
