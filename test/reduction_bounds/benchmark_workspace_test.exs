defmodule ReductionBounds.Benchmark.WorkspaceTest do
  use ExUnit.Case, async: true

  alias ReductionBounds.Benchmark.Workspace

  @tag :tmp_dir
  test "repairs a relative Mix priv link through a temporary-directory alias", %{tmp_dir: dir} do
    source = Path.join(dir, "source/priv")
    physical = Path.join(dir, "physical/temporary")
    temporary_alias = Path.join(dir, "temporary")
    File.mkdir_p!(physical)
    File.ln_s!(physical, temporary_alias)
    build = Path.join(temporary_alias, "build")
    destination = Path.join([build, "lib", "reduction_bounds", "priv"])
    relative = "lean/reduction_bounds/IntegerSize.lean"
    File.mkdir_p!(Path.join(source, "lean/reduction_bounds"))
    File.write!(Path.join(source, relative), "-- packaged source\n")
    File.write!(Path.join(source, "other-resource"), "resource")
    File.mkdir_p!(Path.dirname(destination))
    Mix.Utils.symlink_or_copy(source, destination)
    assert {:ok, _relative_link} = File.read_link(destination)
    refute File.exists?(Path.join(destination, relative))

    assert :ok = Workspace.copy_priv!(build, source)
    assert {:error, :einval} = File.read_link(destination)
    assert File.read!(Path.join(destination, relative)) == File.read!(Path.join(source, relative))
    assert File.read!(Path.join(destination, "other-resource")) == "resource"
    assert File.read!(Path.join(source, relative)) == "-- packaged source\n"
  end

  @tag :tmp_dir
  test "does not copy through a valid link into the source directory", %{tmp_dir: dir} do
    source = Path.join(dir, "priv")
    build = Path.join(dir, "build")
    destination = Path.join([build, "lib", "reduction_bounds", "priv"])
    File.mkdir_p!(source)
    File.write!(Path.join(source, "resource"), "original")
    File.mkdir_p!(Path.dirname(destination))
    File.ln_s!(source, destination)

    assert :ok = Workspace.copy_priv!(build, source)
    File.write!(Path.join(destination, "resource"), "isolated")
    assert File.read!(Path.join(source, "resource")) == "original"
  end

  @tag :tmp_dir
  test "missing source resources fail during preparation", %{tmp_dir: dir} do
    assert_raise File.CopyError, fn ->
      Workspace.copy_priv!(Path.join(dir, "build"), Path.join(dir, "missing"))
    end
  end
end
