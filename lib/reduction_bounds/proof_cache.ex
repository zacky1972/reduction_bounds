defmodule ReductionBounds.ProofCache do
  @moduledoc false

  @version 1
  @runtime_imports ~w(Erlang.erlang Erlang.maps Erlang.lists)
  @header "module\n\n@[expose] public section\n"

  @spec finalize([map()], keyword(), boolean() | :shared) :: [map()]
  def finalize(files, options, policy) do
    names = Enum.map(files, &Map.fetch!(&1, "module"))

    if length(names) != MapSet.size(MapSet.new(names)),
      do: raise(ArgumentError, "duplicate verification module identity")

    pilot? = Enum.any?(names, &String.starts_with?(&1, "ReductionBounds.Proofs."))
    options = Map.new(options)

    {files, _keys} =
      Enum.map_reduce(files, %{}, fn input, keys ->
        file = Map.delete(input, "cache_key")
        dependencies = Enum.map(file["imports"], &dependency(&1, file["module"], names, keys))

        enabled? =
          pilot? and policy != false and
            (policy != :shared or String.starts_with?(file["module"], "ReductionBounds.Proofs."))

        # Lynx partitions by Lean version, compiled Lynx runtime hashes, and
        # effective options. Arbitrary external imports are not in that fingerprint:
        # fail closed by leaving the module and its dependents uncached.
        key =
          if enabled? and Enum.all?(dependencies, &(elem(&1, 1) != nil)) and known_header?(file) do
            :crypto.hash(
              :sha256,
              :erlang.term_to_binary({@version, file, options, dependencies}, [:deterministic])
            )
            |> Base.encode16(case: :lower)
          end

        output = if key, do: Map.put(file, "cache_key", key), else: file
        {output, Map.put(keys, file["module"], key)}
      end)

    files
  end

  defp dependency(name, current, names, keys) do
    cond do
      name == current and String.starts_with?(name, "Erlang.") ->
        # The runner resolves Erlang self-imports to its bundled runtime model.
        {name, if(name in @runtime_imports, do: :lynx_runtime)}

      name in names ->
        unless Map.has_key?(keys, name),
          do: raise(ArgumentError, "verification dependency must precede its consumer: #{name}")

        {name, keys[name]}

      name in @runtime_imports ->
        {name, :lynx_runtime}

      String.starts_with?(name, "ReductionBounds.Proofs.") ->
        raise ArgumentError, "missing shared verification dependency: #{name}"

      true ->
        {name, nil}
    end
  end

  defp known_header?(%{"preludes" => [%{"source" => @header} | _]}), do: true
  defp known_header?(file), do: Map.get(file, "preludes", []) == []
end
