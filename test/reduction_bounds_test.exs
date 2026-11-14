defmodule ReductionBoundsTest do
  use ExUnit.Case

  import Lynx.Lean

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
             ReductionBounds.verify("timeout.lean", [identity, wrapper],
               max_concurrency: 2,
               timeout: 2_000
             )
  end

  test "verifies a module compiled only in memory from its BEAM binary" do
    beam = compile_fixture_in_memory()
    target = {Fixture, :identity, 1}
    on_exit(&unload_fixture/0)

    assert :code.which(Fixture) == []

    assert {:ok, [{^target, {:ok, reports}}]} =
             ReductionBounds.verify("identity.lean", [target], beam_binaries: [beam])

    assert Enum.any?(reports, &match?(%{module: "Erlang.postlude", status: :ok}, &1))
    assert :code.which(Fixture) == []
  end

  test "verifies inline Lean against a recursive in-memory function" do
    beam = compile_fixture_in_memory()
    target = {Fixture, :sum, 1}
    on_exit(&unload_fixture/0)

    postlude = ~LEAN"""
    theorem sumZero :
        Elixir.ReductionBoundsTest.Fixture.«sum/1» (.integer 0) = .ok (.integer 0) := by
      rw [Elixir.ReductionBoundsTest.Fixture.«sum/1».eq_def]
      rfl
    """

    assert {:ok, [{^target, {:ok, reports}}]} =
             ReductionBounds.verify([target],
               postlude: postlude,
               beam_binaries: [beam],
               termination_suffixes: %{target => ~LEAN"partial_fixpoint"}
             )

    assert Enum.any?(reports, &match?(%{module: "Erlang.postlude", status: :ok}, &1))
    assert :code.which(Fixture) == []
  end

  test "requires a Lynx.Lean postlude for inline verification" do
    target = {Fixture, :identity, 1}
    assert {:error, :missing_postlude} = ReductionBounds.verify([target], [])

    assert {:error, {:invalid_option, :postlude, "invalid"}} =
             ReductionBounds.verify([target], postlude: "invalid")
  end

  test "reports a BEAM registration failure" do
    assert {:error, {:beam_registration, %CompileError{}}} =
             ReductionBounds.verify("identity.lean", [{Fixture, :identity, 1}],
               beam_binaries: ["invalid BEAM"]
             )
  end

  test "infers and verifies a symbolic bound for integer list search" do
    beam = compile_fixture_in_memory()
    on_exit(&unload_fixture/0)
    target = {Fixture, :contains, 2}

    assert {:ok, result} =
             ReductionBounds.infer_search_bound(target, beam_binaries: [beam])

    assert result.metric == :symbolic_cost

    assert result.recurrence == %{
             empty: :c_empty,
             hit: :c_hit,
             miss: {:add, :c_step, {:cost, :tail}}
           }

    assert result.upper_bound == {:add, {:max, :c_empty, :c_hit}, {:mul, :n, :c_step}}
    assert Enum.any?(result.reports, &match?(%{module: "Erlang.postlude", status: :ok}, &1))
  end

  test "rejects a search whose recursive call does not consume the tail" do
    beam = compile_fixture_in_memory()
    on_exit(&unload_fixture/0)

    assert {:error, :unsupported_search_shape} =
             ReductionBounds.infer_search_bound({Fixture, :no_progress, 2}, beam_binaries: [beam])
  end

  test "reuses traversal rules for search and non-tail-recursive length" do
    beam = compile_fixture_in_memory()
    on_exit(&unload_fixture/0)

    assert {:ok, search} =
             ReductionBounds.infer_list_bound({Fixture, :contains, 2}, beam_binaries: [beam])

    assert {:ok, length} =
             ReductionBounds.infer_list_bound({Fixture, :list_length, 1}, beam_binaries: [beam])

    assert search.value_model == :membership
    assert length.value_model == :length

    assert [
             {:empty, empty, 0},
             {:guarded_cons, hit, 0},
             {:cons, miss, 1}
           ] = search.recurrence

    assert search.refined_upper_bound ==
             {:if_zero, :n, empty,
              {:max, {:add, empty, {:mul, :n, miss}}, {:add, hit, {:mul, {:sub, :n, 1}, miss}}}}

    assert length.refined_upper_bound == length.upper_bound

    assert [
             {:empty, _, 0},
             {:cons, {:add, _, {:add, {:charge, 1, :recursive_call}, {:charge, 1, :addition}}}, 1}
           ] = length.recurrence

    for result <- [search, length] do
      assert result.metric == :symbolic_cost
      assert {:add, _, {:mul, :n, _}} = result.upper_bound
      assert Enum.any?(result.reports, &match?(%{module: "Erlang.postlude", status: :ok}, &1))
    end
  end

  test "shared rules reject recursion that does not consume the tail" do
    beam = compile_fixture_in_memory()
    on_exit(&unload_fixture/0)

    assert {:error, {:unsupported_list_shape, 2}} =
             ReductionBounds.infer_list_bound({Fixture, :no_progress, 2}, beam_binaries: [beam])
  end

  test "checks a user input contract and reuses the traversal theorem in a local wrapper" do
    beam = compile_fixture_in_memory()
    on_exit(&unload_fixture/0)
    callee = {Fixture, :list_length, 1}
    caller = {Fixture, :forward_length, 1}

    contract = ~LEAN"""
    def inputPrecondition (xs : List Int) : Prop := xs.length < 100
    def inputInvariant (xs : List Int) : Prop := xs.length < 100
    def inputSize (xs : List Int) : Nat := xs.length + 2

    theorem inputInvariantInit (xs : List Int) :
        inputPrecondition xs → inputInvariant xs := id

    theorem inputInvariantTail (head : Int) (tail : List Int) :
        inputInvariant (head :: tail) → inputInvariant tail := by
      simp [inputInvariant]
      omega

    theorem inputSizeTail (head : Int) (tail : List Int) :
        inputInvariant (head :: tail) → inputSize tail + 1 ≤ inputSize (head :: tail) := by
      simp [inputSize] <;> omega
    """

    options = [beam_binaries: [beam], input_contract: contract]
    assert {:ok, direct} = ReductionBounds.infer_list_bound(callee, options)
    assert direct.size_measure == :input_size
    assert {:ok, result} = ReductionBounds.infer_list_call_bound(caller, callee, options)
    assert result.size_measure == :input_size
    assert result.upper_bound == {:add, :caller_cost, direct.refined_upper_bound}

    assert {:ok, %{size_measure: :list_length}} =
             ReductionBounds.infer_list_call_bound(caller, callee, beam_binaries: [beam])

    assert {:error, :unsupported_forwarding_call} =
             ReductionBounds.infer_list_call_bound({Fixture, :constant, 0}, callee, options)

    incomplete = %{
      contract
      | source: String.replace(contract.source, "simp [inputSize] <;> omega", "sorry")
    }

    assert {:error, {:verification_failed, _}} =
             ReductionBounds.infer_list_bound(
               callee,
               Keyword.put(options, :input_contract, incomplete)
             )

    assert {:error, {:verification_failed, _}} =
             ReductionBounds.infer_list_bound(callee,
               beam_binaries: [beam],
               input_contract: ~LEAN"def inputSize (_ : List Int) : Nat := 0"
             )
  end

  defp compile_fixture(directory) do
    beam = compile_fixture_in_memory()
    beam_path = Path.join(directory, "#{Fixture}.beam")
    File.write!(beam_path, beam)
    unload_fixture()
    {:module, Fixture} = :code.load_binary(Fixture, String.to_charlist(beam_path), beam)
    on_exit(&unload_fixture/0)
  end

  defp compile_fixture_in_memory do
    source = """
    defmodule ReductionBoundsTest.Fixture do
      @compile :debug_info
      def identity(value), do: value
      def constant, do: true
      def contains(_key, []), do: false
      def contains(key, [head | _]) when head === key, do: true
      def contains(key, [_ | tail]), do: contains(key, tail)

      def no_progress(_key, []), do: false
      def no_progress(key, [head | _]) when head === key, do: true
      def no_progress(key, [_ | _] = list), do: no_progress(key, list)

      def list_length([]), do: 0
      def list_length([_ | tail]), do: 1 + list_length(tail)
      def forward_length(xs), do: list_length(xs)

      def sum(0), do: 0
      def sum(n), do: sum(n - 1) + n
      def identity_wrapper(value), do: identity(value)
    end
    """

    [{Fixture, beam}] = Code.compile_string(source)
    beam
  end

  defp unload_fixture do
    :code.delete(Fixture)
    :code.purge(Fixture)
  end
end
