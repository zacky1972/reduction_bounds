# cspell:words leanj
defmodule ReductionBounds.Verification do
  @moduledoc false

  alias ReductionBounds.{ProofCache, ProofModules}

  @typep translation :: %Lynx.Translation{}

  @fragment_imports ["Erlang.erlang", "Erlang.maps"]

  @spec assemble(translation(), keyword()) :: [map()]
  def assemble(translation, opts \\ []) do
    {translation, imports} = prepare(translation, opts)

    {translation, shared} =
      if embedded?(opts),
        do: {translation, []},
        else: ProofModules.split(translation, opts[:definition])

    translation =
      if shared != [] and translation.postludes != [] do
        origin = List.last(translation.postludes).file
        %{translation | postludes: translation.postludes ++ [ProofModules.audit(origin)]}
      else
        translation
      end

    shared_imports = Enum.map(shared, & &1["module"])

    files =
      translation
      |> Lynx.Translation.assemble(cache: false)
      |> Enum.map(fn
        %{"module" => "Erlang.postlude"} = file ->
          Map.update!(file, "imports", &Enum.uniq(imports ++ shared_imports ++ &1))

        file ->
          file
      end)

    ProofCache.finalize(shared ++ files, Keyword.get(opts, :options, []), cache_policy(opts))
  end

  defp embedded?(opts) do
    Keyword.get(
      opts,
      :shared_modules,
      System.get_env("REDUCTION_BOUNDS_PROOF_MODE") != "embedded"
    ) == false
  end

  defp cache_policy(opts) do
    Keyword.get_lazy(opts, :cache, fn ->
      case System.get_env("REDUCTION_BOUNDS_PROOF_CACHE", "on") do
        "on" -> true
        "off" -> false
        "shared" -> :shared
        value -> raise ArgumentError, "invalid REDUCTION_BOUNDS_PROOF_CACHE: #{inspect(value)}"
      end
    end)
  end

  @spec verify!(translation() | [map()], keyword()) :: [map()]
  def verify!(input, opts \\ []) do
    case System.get_env("REDUCTION_BOUNDS_BENCH_EVENTS") do
      nil -> run(input, opts)
      path -> measured(input, opts, path)
    end
  end

  @spec project_dir() :: String.t()
  def project_dir(), do: Path.join(Mix.Project.deps_paths()[:lynx], "Lean")

  defp run(input, opts) do
    input |> files(opts) |> invoke(opts)
  end

  defp files(%Lynx.Translation{} = translation, opts), do: assemble(translation, opts)

  defp files(files, opts) when is_list(files),
    do: ProofCache.finalize(files, Keyword.get(opts, :options, []), cache_policy(opts))

  defp invoke(files, opts) do
    Lynx.Commands.verify!(project_dir(), files, options: Keyword.get(opts, :options, []))
  end

  defp prepare(translation, opts) do
    imports = Keyword.get(opts, :postlude_imports, [])

    case Keyword.get(opts, :definition) do
      :translated ->
        {translate(translation, opts), imports}

      :composed ->
        {translate(translation, opts), ["Erlang.lists" | imports]}

      :circular_buffer_model ->
        {translation, ["Erlang.lists" | imports]}

      fragment when fragment in [:struct_fragment, :execution_fragment] ->
        {translation, @fragment_imports ++ imports}

      :lynx_builtin ->
        {module, _, _} = Keyword.fetch!(opts, :target)
        {translation, [:lynx_core_to_leanj.module_name(module) | imports]}

      _ ->
        {translation, imports}
    end
  end

  defp translate(translation, opts) do
    {module, function, arity} = Keyword.fetch!(opts, :target)
    Lynx.Translation.translate(translation, module, [{function, arity}])
  end

  defp measured(input, opts, path) do
    id = "#{System.pid()}-#{System.unique_integer([:positive, :monotonic])}"
    emit(path, %{id: id, event: :started, target: inspect(opts[:target])})
    started = now()

    try do
      files = files(input, opts)
      assembled = now()
      reports = invoke(files, opts)
      finished = now()
      runner_ms = milliseconds(finished - assembled)
      module_ms = Enum.sum(Enum.map(reports, & &1.time_ms))

      emit(path, %{
        id: id,
        event: :completed,
        assembly_ms: milliseconds(assembled - started),
        runner_wall_ms: runner_ms,
        module_wall_ms: module_ms,
        runner_non_module_wall_ms: max(0, runner_ms - module_ms),
        reports:
          Enum.map(reports, &Map.take(&1, [:module, :status, :cached, :time_ms, :theorems]))
      })

      reports
    catch
      kind, reason ->
        emit(path, %{
          id: id,
          event: :failed,
          wall_ms: milliseconds(now() - started),
          kind: kind,
          reason: Exception.format_banner(kind, reason)
        })

        :erlang.raise(kind, reason, __STACKTRACE__)
    end
  end

  defp now(), do: System.monotonic_time()

  defp milliseconds(duration),
    do: System.convert_time_unit(duration, :native, :microsecond) / 1000

  # Measurement must never turn an accepted/rejected proof into a different result.
  defp emit(path, event) do
    :global.trans({{__MODULE__, path}, self()}, fn ->
      File.write(path, [JSON.encode!(event), "\n"], [:append])
    end)
  rescue
    _error -> :ok
  end
end
