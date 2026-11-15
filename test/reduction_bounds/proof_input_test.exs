defmodule ReductionBounds.ProofInputTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.ProofInput

  test "loads the packaged Lean sources in dependency order" do
    lean_dir =
      Path.join([List.to_string(:code.priv_dir(:reduction_bounds)), "lean", "reduction_bounds"])

    assert {:ok, [core, rules, normalize, _proof]} = ProofInput.postludes(proof())

    for {block, name} <- [
          {core, "CoreFragment.lean"},
          {rules, "StructRules.lean"},
          {normalize, "Normalize.lean"}
        ] do
      path = Path.join(lean_dir, name)

      assert block == %Lynx.Lean{
               file: path,
               source: File.read!(path),
               span: {1, 1},
               indentation: 0
             }
    end
  end

  test "appends the generated proof with its original location" do
    proof = proof()

    assert {:ok, [_core, _rules, _normalize, ^proof]} = ProofInput.postludes(proof)
  end

  @tag :tmp_dir
  test "reports the path and reason for an unreadable common source", %{tmp_dir: priv_dir} do
    lean_dir = Path.join([priv_dir, "lean", "reduction_bounds"])
    File.mkdir_p!(lean_dir)
    File.write!(Path.join(lean_dir, "CoreFragment.lean"), "-- First source")
    path = Path.join(lean_dir, "StructRules.lean")

    assert {:error, {:read_lean, ^path, :enoent}} = ProofInput.postludes(proof(), priv_dir)
  end

  defp proof() do
    %Lynx.Lean{
      file: "generated/target.lean",
      source: "theorem sample : True := by trivial",
      span: {7, 5},
      indentation: 4
    }
  end
end
