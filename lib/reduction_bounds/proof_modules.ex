defmodule ReductionBounds.ProofModules do
  @moduledoc false

  @typep translation :: %Lynx.Translation{}

  @entries [
    %{
      id: :integer_size,
      module: "ReductionBounds.Proofs.IntegerSize",
      source: "IntegerSize.lean",
      imports: []
    },
    %{
      id: :integer_analysis,
      module: "ReductionBounds.Proofs.IntegerAnalysis",
      source: "IntegerAnalysis.lean",
      imports: [:integer_size]
    },
    %{
      id: :integer_cost,
      module: "ReductionBounds.Proofs.IntegerCost",
      source: "IntegerCost.lean",
      imports: [:integer_size, :integer_analysis]
    },
    %{
      id: :integer_cost_source,
      module: "ReductionBounds.Proofs.IntegerCostSource",
      source: "IntegerCostSource.lean",
      imports: [:integer_size, :integer_analysis, :integer_cost]
    }
  ]

  @spec entries() :: [map()]
  def entries(), do: @entries

  @spec closure([atom()], [map()]) :: [map()]
  def closure(roots, entries \\ @entries) do
    for field <- [:id, :module, :source] do
      values = Enum.map(entries, &Map.fetch!(&1, field))

      if length(values) != MapSet.size(MapSet.new(values)),
        do: raise(ArgumentError, "duplicate shared module #{field}")
    end

    registry = Map.new(entries, &{&1.id, &1})
    # Validate every entry, including nodes not selected by this workflow.
    _validated = Enum.reduce(Map.keys(registry), {[], MapSet.new()}, &visit(&1, &2, registry, []))
    {ordered, _} = Enum.reduce(roots, {[], MapSet.new()}, &visit(&1, &2, registry, []))
    Enum.reverse(ordered)
  end

  defp visit(id, {ordered, done} = state, registry, pending) do
    if id in pending, do: raise(ArgumentError, "cyclic shared module dependency: #{inspect(id)}")
    entry = Map.get(registry, id) || raise(ArgumentError, "missing shared module: #{inspect(id)}")

    if MapSet.member?(done, id) do
      state
    else
      {ordered, done} =
        Enum.reduce(entry.imports, {ordered, done}, &visit(&1, &2, registry, [id | pending]))

      {[entry | ordered], MapSet.put(done, id)}
    end
  end

  @workflows %{
    integer_fragment: [:integer_analysis],
    integer_cost_fragment: [:integer_cost_source],
    integer_bound_transfer: [:integer_cost_source],
    cost_contract_comparison: [:integer_cost]
  }

  @spec split(translation(), atom() | nil) :: {translation(), [map()]}
  def split(translation, workflow \\ nil) do
    paths = Map.new(@entries, &{source_path(&1.source), &1.id})
    sources = Enum.filter(translation.postludes, &Map.has_key?(paths, Path.expand(&1.file)))

    # Protocol families also embed IntegerSize; keep those on the original path
    # until they are migrated together. Integer consumers carry IntegerAnalysis.
    roots = Map.get(@workflows, workflow, [])

    if roots != [] or Enum.any?(sources, &(paths[Path.expand(&1.file)] != :integer_size)) do
      files = shared_files(sources, paths, roots)
      remaining = Enum.reject(translation.postludes, &Map.has_key?(paths, Path.expand(&1.file)))
      {%{translation | postludes: remaining}, files}
    else
      {translation, []}
    end
  end

  defp shared_files(sources, paths, roots) do
    selected = Enum.map(sources, &paths[Path.expand(&1.file)])

    if length(selected) != MapSet.size(MapSet.new(selected)),
      do: raise(ArgumentError, "duplicate shared source in proof input")

    blocks = Map.new(sources, &{paths[Path.expand(&1.file)], &1})
    ordered = closure(roots ++ selected)
    registry = Map.new(@entries, &{&1.id, &1.module})

    Enum.map(ordered, fn entry ->
      block =
        Map.get(blocks, entry.id) ||
          raise(ArgumentError, "missing shared source: #{entry.source}")

      named_file(entry, block, registry)
    end)
  end

  @spec source_path(String.t()) :: String.t()
  def source_path(source) do
    :reduction_bounds
    |> :code.priv_dir()
    |> List.to_string()
    |> Path.join("lean/reduction_bounds/#{source}")
    |> Path.expand()
  end

  defp named_file(entry, block, registry) do
    # Produce prelude blocks through Lynx's public assembler and submit the
    # documented named-module protocol through Lynx.Commands.verify!/3.
    [file] =
      Lynx.Translation.new(postludes: [block, audit(block.file)])
      |> Lynx.Translation.assemble(cache: false)

    %{
      file
      | "module" => entry.module,
        "imports" => Enum.map(entry.imports, &Map.fetch!(registry, &1))
    }
  end

  @spec audit(String.t()) :: Lynx.Lean.t()
  def audit(file) do
    source = """
    open Lean in
    run_cmd do
      let env := (← getEnv).setExporting false
      for (name, _) in env.constants.toList do
        if (env.find? name).isSome && (env.getModuleIdxFor? name).isNone then
          for dependency in ← collectAxioms name do
            unless #[``propext, ``Classical.choice, ``Quot.sound].contains dependency do
              throwError m!"Unexpected axiom in {name}: {dependency}"
    """

    %Lynx.Lean{source: source, file: file <> ".audit", span: {1, 1}, indentation: 0}
  end
end
