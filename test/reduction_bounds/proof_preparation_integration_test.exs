defmodule ReductionBounds.ProofPreparationIntegrationTest do
  use ExUnit.Case, async: true
  @moduletag timeout: 300_000

  alias ReductionBounds.{ProofCache, ProofInput, Verification}

  test "concurrent distinct targets compile a cold shared closure once" do
    nonce = Base.encode16(:crypto.strong_rand_bytes(12))
    first = integer_input("theorem preparedFirst : True := by trivial", nonce)
    second = integer_input("theorem preparedSecond : True := by trivial", nonce)

    results =
      [first, second]
      |> Task.async_stream(&Verification.verify!(&1, cache: true, shared_modules: true),
        max_concurrency: 2,
        timeout: 60_000
      )
      |> Enum.map(fn {:ok, reports} -> reports end)

    assert Enum.all?(List.flatten(results), &(&1.status == :ok))

    cold =
      Enum.count(results, fn reports -> Enum.any?(Enum.drop(reports, -1), &(not &1.cached)) end)

    assert cold == 1
    assert Enum.all?(results, &(not List.last(&1).cached))
  end

  @tag :tmp_dir
  test "readiness context changes with compiled dependency identities", %{tmp_dir: dir} do
    path = Path.join(dir, ".lake/build/lib/lean/Model.olean.hash")
    File.mkdir_p!(Path.dirname(path))
    File.write!(path, "original")
    first = ProofCache.preparation_context(dir)
    File.write!(path, "changed")
    refute first == ProofCache.preparation_context(dir)
    File.rm!(path)
    refute first == ProofCache.preparation_context(dir)
  end

  defp integer_input(source, nonce) do
    proof = %Lynx.Lean{
      source: source,
      file: "coordinated_target.lean",
      span: {1, 1},
      indentation: 0
    }

    {:ok, [size | rest]} = ProofInput.integer_postludes(proof)
    size = %{size | source: size.source <> "\n-- #{nonce}\n"}
    Lynx.Translation.new(postludes: [size | rest])
  end
end
