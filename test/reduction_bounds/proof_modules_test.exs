defmodule ReductionBounds.ProofModulesTest do
  use ExUnit.Case, async: true
  alias ReductionBounds.{ProofCache, ProofInput, ProofModules, Verification}

  test "registry resolves direct dependency closures and rejects invalid identities and graphs" do
    assert Enum.map(ProofModules.closure([:integer_analysis]), & &1.id) ==
             [:integer_size, :integer_analysis]

    assert length(ProofModules.closure([:integer_cost_source, :integer_size])) == 4
    entries = ProofModules.entries()

    assert_raise ArgumentError, ~r/duplicate/, fn ->
      ProofModules.closure([], entries ++ entries)
    end

    [first | rest] = entries

    assert_raise ArgumentError, ~r/missing/, fn ->
      ProofModules.closure([], [%{first | imports: [:missing]} | rest])
    end

    assert_raise ArgumentError, ~r/cyclic/, fn ->
      ProofModules.closure([], [%{first | imports: [:integer_cost]} | rest])
    end
  end

  test "final keys cover complete module inputs, ordered dependencies, and options" do
    files = assemble(translation())
    assert length(files) == 3
    assert Enum.all?(files, &Map.has_key?(&1, "cache_key"))
    [size, analysis, target] = files

    changed =
      update_in(target, ["preludes", Access.at(1), "source"], &(&1 <> "\n-- different target"))

    [same_size, same_analysis, new_target] =
      ProofCache.finalize([size, analysis, changed], [], true)

    assert same_size["cache_key"] == size["cache_key"]
    assert same_analysis["cache_key"] == analysis["cache_key"]
    refute new_target["cache_key"] == target["cache_key"]

    changed =
      update_in(size, ["preludes", Access.at(1), "source"], &(&1 <> "\n-- different theory"))

    updated = ProofCache.finalize([changed, analysis, target], [], true)

    assert Enum.zip_with(files, updated, &(&1["cache_key"] != &2["cache_key"])) == [
             true,
             true,
             true
           ]

    for change <- [
          fn file -> Map.put(file, "file", "different.lean") end,
          fn file -> put_in(file, ["preludes", Access.at(1), "span"], [42, 3]) end,
          fn file -> Map.put(file, "imports", Enum.reverse(file["imports"])) end
        ] do
      updated = ProofCache.finalize([size, analysis, change.(target)], [], true)
      refute List.last(updated)["cache_key"] == target["cache_key"]
    end

    updated = ProofCache.finalize(files, [maxRecDepth: 10001], true)

    assert Enum.zip_with(files, updated, &(&1["cache_key"] != &2["cache_key"])) == [
             true,
             true,
             true
           ]

    assert Enum.all?(ProofCache.finalize(files, [], false), &(not Map.has_key?(&1, "cache_key")))

    assert [%{"cache_key" => _}, %{"cache_key" => _}, shared_only] =
             ProofCache.finalize(files, [], :shared)

    refute Map.has_key?(shared_only, "cache_key")
  end

  test "untracked external imports disable reuse for their consumers and dependents" do
    [size, analysis, target] = assemble(translation())

    updated =
      ProofCache.finalize([%{size | "imports" => ["Custom.Theory"]}, analysis, target], [], true)

    assert Enum.all?(updated, &(not Map.has_key?(&1, "cache_key")))

    assert_raise ArgumentError, ~r/precede/, fn ->
      ProofCache.finalize([analysis, size, target], [], true)
    end

    assert_raise ArgumentError, ~r/missing/, fn ->
      ProofCache.finalize([analysis, target], [], true)
    end

    assert_raise ArgumentError, ~r/duplicate/, fn ->
      ProofCache.finalize([size, size], [], true)
    end
  end

  test "bypass and embedded paths retain the proof and its diagnostic origins" do
    input = translation()
    named = assemble(input, cache: false)
    embedded = assemble(input, shared_modules: false)
    assert length(embedded) == 1
    assert Enum.all?(named ++ embedded, &(not Map.has_key?(&1, "cache_key")))
    source = hd(input.postludes)
    assert get_in(hd(named), ["preludes", Access.at(1), "file"]) == source.file
    assert get_in(hd(named), ["preludes", Access.at(1), "source"]) == source.source

    assert get_in(List.last(named), ["preludes", Access.at(1), "source"]) ==
             List.last(input.postludes).source
  end

  test "assembly rejects duplicate shared sources and missing prerequisites before invoking Lean" do
    input = translation()
    [size, analysis, proof] = input.postludes

    assert_raise ArgumentError, ~r/duplicate shared source/, fn ->
      assemble(%{input | postludes: [size, size, analysis, proof]})
    end

    assert_raise ArgumentError, ~r/missing shared source/, fn ->
      assemble(%{input | postludes: [analysis, proof]})
    end

    assert_raise ArgumentError, ~r/missing shared source/, fn ->
      assemble(%{input | postludes: [proof]}, definition: :integer_fragment)
    end
  end

  test "Erlang self-imports retain the runner's runtime-resolution semantics" do
    [size | _] = assemble(translation())

    builtin = %{
      "module" => "Erlang.maps",
      "file" => "maps.erl",
      "imports" => ["Erlang.maps"],
      "contents" => []
    }

    assert [_, %{"cache_key" => _}] = ProofCache.finalize([size, builtin], [], true)
    unknown = %{builtin | "module" => "Erlang.custom", "imports" => ["Erlang.custom"]}
    assert [_, uncached] = ProofCache.finalize([size, unknown], [], true)
    refute Map.has_key?(uncached, "cache_key")
  end

  defp assemble(input, opts \\ []) do
    Verification.assemble(input, Keyword.merge([cache: true, shared_modules: true], opts))
  end

  defp translation do
    proof = %Lynx.Lean{
      source: "theorem cacheCheck : True := by trivial",
      file: "cache_check.lean",
      span: {1, 1},
      indentation: 0
    }

    {:ok, postludes} = ProofInput.integer_postludes(proof)
    Lynx.Translation.new(postludes: postludes)
  end
end
