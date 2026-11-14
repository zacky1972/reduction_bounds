defmodule ReductionBoundsTest do
  use ExUnit.Case

  doctest ReductionBounds

  alias ReductionBoundsTest.Fixture

  @tag :tmp_dir
  test "verifies each distinct target once in first-occurrence order", %{tmp_dir: directory} do
    compile_fixture(directory)
    identity = {Fixture, :identity, 1}
    wrapper = {Fixture, :identity_wrapper, 1}

    assert {:ok, [{^identity, {:ok, first}}, {^wrapper, {:ok, second}}]} =
             ReductionBounds.verify("identity.lean", [identity, wrapper, wrapper, identity],
               max_concurrency: 2,
               lean_options: [maxHeartbeats: 200_000]
             )

    for reports <- [first, second] do
      assert Enum.any?(reports, &match?(%{module: "Erlang.postlude", status: :ok}, &1))
    end
  end

  @tag :tmp_dir
  test "a translation error does not prevent verification of another target", %{
    tmp_dir: directory
  } do
    compile_fixture(directory)
    missing_function = {Fixture, :missing, 1}
    missing_module = {ReductionBoundsTest.MissingModule, :identity, 1}
    target = {Fixture, :identity, 1}

    assert {:ok,
            [
              {^missing_function, {:error, {:lynx, %CompileError{description: function_error}}}},
              {^missing_module, {:error, {:lynx, %CompileError{description: module_error}}}},
              {^target, {:ok, _reports}}
            ]} =
             ReductionBounds.verify("identity.lean", [missing_function, missing_module, target])

    assert function_error =~ "undefined function"
    assert module_error =~ "unknown module"
  end

  @tag :tmp_dir
  test "reports a Lean error for the affected target", %{tmp_dir: directory} do
    compile_fixture(directory)
    identity = {Fixture, :identity, 1}
    constant = {Fixture, :constant, 0}

    assert {:ok, [{^identity, {:ok, _}}, {^constant, {:error, {:verification_failed, reports}}}]} =
             ReductionBounds.verify("identity.lean", [identity, constant])

    assert Enum.any?(reports, &match?(%{module: "Erlang.postlude", status: :error}, &1))
  end

  test "returns the underlying reason when the Lean file cannot be read" do
    assert {:error, {:read_lean, path, :enoent}} =
             ReductionBounds.verify("nonexistent.lean", [{Fixture, :identity, 1}])

    assert Path.basename(path) == "nonexistent.lean"
  end

  test "restricts proof filenames to the project lean directory" do
    assert {:error, :invalid_lean_path} =
             ReductionBounds.verify("../mix.exs", [{Fixture, :identity, 1}])
  end

  test "reports malformed target values without positions" do
    invalid_arity = {Fixture, :identity, -1}
    invalid_function = {Fixture, "identity", 1}

    assert {:error, {:invalid_targets, [^invalid_arity, ^invalid_function]}} =
             ReductionBounds.verify("identity.lean", [
               {Fixture, :identity, 1},
               invalid_arity,
               invalid_function,
               invalid_arity
             ])
  end

  test "rejects invalid verification options before starting Lynx" do
    assert {:error, {:invalid_option, :timeout, :infinity}} =
             ReductionBounds.verify("identity.lean", [], timeout: :infinity)

    assert {:error, {:invalid_option, :max_concurrency, 0}} =
             ReductionBounds.verify("identity.lean", [], max_concurrency: 0)
  end

  @tag :tmp_dir
  test "keeps each target when its verification times out", %{tmp_dir: directory} do
    compile_fixture(directory)
    identity = {Fixture, :identity, 1}
    wrapper = {Fixture, :identity_wrapper, 1}

    assert {:ok, [{^identity, {:error, :timeout}}, {^wrapper, {:error, :timeout}}]} =
             ReductionBounds.verify("identity.lean", [identity, wrapper],
               max_concurrency: 1,
               timeout: 1
             )
  end

  defp compile_fixture(directory) do
    source = """
    defmodule ReductionBoundsTest.Fixture do
      @compile :debug_info
      def identity(value), do: value
      def constant, do: true
      def identity_wrapper(value), do: identity(value)
    end
    """

    [{Fixture, beam}] = Code.compile_string(source)
    beam_path = Path.join(directory, "#{Fixture}.beam")
    File.write!(beam_path, beam)
    :code.delete(Fixture)
    :code.purge(Fixture)
    {:module, Fixture} = :code.load_binary(Fixture, String.to_charlist(beam_path), beam)

    on_exit(fn ->
      :code.delete(Fixture)
      :code.purge(Fixture)
    end)
  end
end
