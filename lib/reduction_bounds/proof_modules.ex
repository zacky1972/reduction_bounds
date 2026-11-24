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
    },
    %{
      id: :core_fragment,
      module: "ReductionBounds.Proofs.CoreFragment",
      source: "CoreFragment.lean",
      imports: [],
      runtime_imports: ["Erlang.erlang", "Erlang.maps"]
    },
    %{
      id: :struct_rules,
      module: "ReductionBounds.Proofs.StructRules",
      source: "StructRules.lean",
      imports: [:core_fragment],
      runtime_imports: ["Erlang.maps"]
    },
    %{
      id: :normalize,
      module: "ReductionBounds.Proofs.Normalize",
      source: "Normalize.lean",
      imports: [:core_fragment, :struct_rules]
    },
    %{
      id: :execution,
      module: "ReductionBounds.Proofs.ExecutionBound",
      source: "ExecutionBound.lean",
      imports: [:core_fragment, :struct_rules]
    },
    %{
      id: :protocol,
      module: "ReductionBounds.Proofs.Protocol",
      source: "Protocol.lean",
      imports: []
    },
    %{
      id: :rpc_protocol,
      module: "ReductionBounds.Proofs.RpcProtocol",
      source: "RpcProtocol.lean",
      imports: [:protocol]
    },
    %{
      id: :rpc_term,
      module: "ReductionBounds.Proofs.RpcTerm",
      source: "RpcTerm.lean",
      imports: []
    },
    %{
      id: :mailbox,
      module: "ReductionBounds.Proofs.Mailbox",
      source: "Mailbox.lean",
      imports: [:rpc_term]
    },
    %{
      id: :rpc_mailbox,
      module: "ReductionBounds.Proofs.RpcMailbox",
      source: "RpcMailbox.lean",
      imports: [:rpc_protocol, :mailbox]
    },
    %{
      id: :rpc_completion,
      module: "ReductionBounds.Proofs.RpcCompletion",
      source: "RpcCompletion.lean",
      imports: [:rpc_mailbox]
    },
    %{
      id: :rpc_cost,
      module: "ReductionBounds.Proofs.RpcCost",
      source: "RpcCost.lean",
      imports: [:rpc_mailbox]
    },
    %{
      id: :protocol_conditions,
      module: "ReductionBounds.Proofs.ProtocolConditions",
      source: "ProtocolConditions.lean",
      imports: [:integer_size, :protocol]
    },
    %{
      id: :protocol_cost,
      module: "ReductionBounds.Proofs.ProtocolCost",
      source: "ProtocolCost.lean",
      imports: [:integer_size, :protocol, :protocol_conditions]
    },
    %{
      id: :port_completion,
      module: "ReductionBounds.Proofs.PortCompletion",
      source: "PortCompletion.lean",
      imports: [:protocol]
    },
    %{
      id: :port_source,
      module: "ReductionBounds.Proofs.PortSource",
      source: "PortSource.lean",
      imports: [:protocol, :protocol_conditions, :protocol_cost]
    },
    %{
      id: :cost_contract,
      module: "ReductionBounds.Proofs.CostContract",
      source: "CostContract.lean",
      imports: [:integer_cost]
    },
    %{
      id: :bound_transfer,
      module: "ReductionBounds.Proofs.BoundTransfer",
      source: "BoundTransfer.lean",
      imports: [:integer_analysis, :integer_cost, :cost_contract]
    },
    %{
      id: :search,
      module: "ReductionBounds.Proofs.SearchRules",
      source: "SearchRules.lean",
      imports: []
    },
    %{
      id: :list_rules,
      module: "ReductionBounds.Proofs.ListRules",
      source: "ListRules.lean",
      imports: []
    },
    %{
      id: :list_member,
      module: "ReductionBounds.Proofs.ListMember",
      source: "ListMember.lean",
      imports: [:list_rules],
      runtime_imports: ["Erlang.lists", "Erlang.erlang"],
      producer: {ReductionBounds.ComposedBound, :shared_source, [:list_member]}
    },
    %{
      id: :list_reverse,
      module: "ReductionBounds.Proofs.ListReverse",
      source: "ListReverse.lean",
      imports: [:list_rules],
      runtime_imports: ["Erlang.lists"],
      producer: {ReductionBounds.ComposedBound, :shared_source, [:list_reverse]}
    },
    %{
      id: :list_primitives,
      module: "ReductionBounds.Proofs.ListPrimitives",
      source: "ListPrimitives.lean",
      imports: [:list_member, :list_reverse],
      runtime_imports: ["Erlang.lists"],
      producer: {ReductionBounds.ComposedBound, :shared_source, [:list_primitives]}
    },
    %{
      id: :enum_reverse,
      module: "ReductionBounds.Proofs.EnumReverse",
      source: "EnumReverse.lean",
      imports: [:list_reverse],
      producer: {ReductionBounds.ComposedBound, :shared_source, [:enum_reverse]}
    },
    %{
      id: :buffer_paths,
      module: "ReductionBounds.Proofs.BufferPaths",
      source: "BufferPaths.lean",
      imports: [:list_reverse, :enum_reverse],
      producer: {ReductionBounds.ComposedBound, :shared_source, [:buffer_paths]}
    },
    %{
      id: :circular_buffer,
      module: "ReductionBounds.Proofs.CircularBuffer",
      source: "CircularBuffer.lean",
      imports: [:enum_reverse, :buffer_paths]
    },
    %{
      id: :periodic,
      module: "ReductionBounds.Proofs.Periodic",
      source: "Periodic.lean",
      imports: []
    },
    %{
      id: :circular_buffer_sequence,
      module: "ReductionBounds.Proofs.CircularBufferSequence",
      source: "CircularBufferSequence.lean",
      imports: [:circular_buffer, :buffer_paths, :enum_reverse, :list_reverse, :periodic]
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
    integer_bound_transfer: [:integer_cost_source, :bound_transfer],
    cost_contract_comparison: [:bound_transfer],
    struct_fragment: [:normalize],
    execution_fragment: [:normalize, :execution],
    port_completion: [:protocol_cost, :port_completion],
    port_source: [:port_source],
    periodic_fragment: [:periodic],
    composed: [:list_primitives],
    circular_buffer_model: [:circular_buffer]
  }

  @spec split(translation(), atom() | nil) :: {translation(), [map()]}
  def split(translation, workflow \\ nil) do
    paths = Map.new(@entries, &{source_path(&1.source), &1.id})
    sources = Enum.filter(translation.postludes, &Map.has_key?(paths, Path.expand(&1.file)))

    roots = Map.get(@workflows, workflow, [])

    if roots != [] or sources != [] do
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

  @generated %{
    "generated_search_bound.lean" => [:search],
    "generated_list_bound.lean" => [:list_rules],
    "generated_composed_bound.lean" => [:list_primitives],
    "generated_circular_buffer_bound.lean" => [:circular_buffer],
    "generated_circular_buffer_sequence_bound.lean" => [:circular_buffer_sequence],
    "generated_periodic_bound.lean" => [:periodic]
  }

  @spec generated_roots(Lynx.Lean.t()) :: [atom()]
  def generated_roots(proof), do: Map.get(@generated, proof.file, [])

  @spec load([atom()]) :: [Lynx.Lean.t()]
  def load(roots) do
    Enum.map(closure(roots), fn entry ->
      case Map.get(entry, :producer) do
        nil ->
          Lynx.Lean.from_file!(source_path(entry.source))

        {module, function, args} ->
          %Lynx.Lean{
            source: apply(module, function, args),
            file: source_path(entry.source),
            span: {1, 1},
            indentation: 0
          }
      end
    end)
  end

  @spec runtime_imports([Lynx.Lean.t()]) :: [String.t()]
  def runtime_imports(postludes) do
    paths = Map.new(@entries, &{source_path(&1.source), Map.get(&1, :runtime_imports, [])})
    postludes |> Enum.flat_map(&Map.get(paths, Path.expand(&1.file), [])) |> Enum.uniq()
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
        "imports" =>
          Enum.map(entry.imports, &Map.fetch!(registry, &1)) ++
            Map.get(entry, :runtime_imports, [])
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
