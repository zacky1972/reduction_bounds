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

  @tag :case_study
  test "checks symbolic bounds for the built-in lists membership function" do
    target = {:lists, :member, 2}

    assert {:ok, bound} = ReductionBounds.infer_list_bound(target)

    assert_case_study(
      bound,
      target,
      :lynx_builtin,
      "generated_list_bound.lean",
      ~w(listRulesSound listPathBounds searchCostDerivation listValueAndBound)
    )

    assert bound.size_measure == :list_length
    assert bound.value_model == :membership
    assert bound.domain == :proper_integer_list_with_integer_key_if_present
    {empty, hit, step} = member_charges()
    assert bound.recurrence == [{:empty, empty, 0}, {:guarded_cons, hit, 0}, {:cons, step, 1}]
    assert bound.upper_bound == {:add, {:max, empty, hit}, {:mul, :n, step}}

    assert bound.refined_upper_bound == member_contract_upper()
    assert :lists.member(2, []) == false
    assert :lists.member(2, [2, 1]) == true
    assert :lists.member(-1, [2, -1]) == true
    assert :lists.member(2, [1, 3]) == false
  end

  @tag :case_study
  test "checks symbolic bounds for the built-in reversal with an accumulator" do
    target = {:lists, :reverse, 2}

    assert {:ok, bound} = ReductionBounds.infer_list_bound(target)

    assert_case_study(
      bound,
      target,
      :lynx_builtin,
      "generated_list_bound.lean",
      ~w(listRulesSound reverseCostDerivation reverseResult listValueAndBound)
    )

    assert bound.size_measure == :list_length
    assert bound.value_model == :reversal
    assert bound.domain == :proper_integer_lists
    {empty, step} = reverse_charges()
    assert bound.recurrence == [{:empty, empty, 0}, {:cons, step, 1}]
    assert bound.upper_bound == reverse_contract_upper(:n)
    assert bound.refined_upper_bound == bound.upper_bound
    assert :lists.reverse([], [3, 4]) == [3, 4]
    assert :lists.reverse([1, 2], [3, 4]) == [2, 1, 3, 4]
  end

  @tag :case_study
  test "composes bounds for static calls, bindings, and Boolean branches" do
    beam = compile_fixture_in_memory()
    on_exit(&unload_fixture/0)
    options = [beam_binaries: [beam]]
    target = {Fixture, :reverse_on_hit, 2}

    assert {:ok, bound} = ReductionBounds.infer_list_bound(target, options)

    assert_case_study(
      bound,
      target,
      :composed,
      "generated_composed_bound.lean",
      ~w(Member.listValueAndBound Reverse.listValueAndBound programValueAndBound)
    )

    assert Enum.any?(bound.reports, &(&1.module == Atom.to_string(Fixture) and &1.status == :ok))
    assert bound.value_model == :composed
    assert bound.domain == :proper_integer_list_with_integer_key_if_present
    assert bound.size_measure == :list_length
    paths = bound.path_bounds

    search = {:call_bound, {:lists, :member, 2}, member_contract_upper()}
    reversal = {:call_bound, {:lists, :reverse, 2}, reverse_contract_upper(:n)}
    hit = {:add, search, {:add, {:branch_cost, :hit}, reversal}}
    miss = {:add, search, {:branch_cost, :miss}}

    assert paths == %{hit: hit, miss: miss}
    assert bound.upper_bound == {:max, hit, miss}
    reverse_on_hit = Function.capture(Fixture, :reverse_on_hit, 2)
    assert reverse_on_hit.(2, [1, 2, 3]) == [3, 2, 1]
    assert reverse_on_hit.(4, [1, 2, 3]) == [1, 2, 3]
    assert reverse_on_hit.(2, []) == []

    assert {:ok, %{value_model: :composed, path_bounds: ^paths}} =
             ReductionBounds.infer_list_bound({Fixture, :reverse_onto_on_hit, 2}, options)

    for name <- [:reverse_via_helper, :reverse_via_case] do
      assert {:ok, %{value_model: :composed, path_bounds: %{hit: hit}}} =
               ReductionBounds.infer_list_bound({Fixture, name, 2}, options)

      assert contains_call_bound?(hit, {Fixture, :reverse_onto, 1})
    end

    assert {:ok, %{value_model: :composed, upper_bound: twice}} =
             ReductionBounds.infer_list_bound({Fixture, :reverse_twice, 1}, options)

    assert {:add, {:call_bound, {:lists, :reverse, 2}, _},
            {:add, {:operation_cost, :bind},
             {:call_bound, {:lists, :reverse, 2}, {:add, _, {:mul, {:add, :n, 1}, _}}}}} =
             twice
  end

  @tag :case_study
  test "checks the symbolic bound for one circular buffer insertion" do
    assert {:ok, bound} = ReductionBounds.infer_circular_buffer_bound()

    assert_case_study(
      bound,
      {CircularBuffer, :insert, 2},
      :circular_buffer_model,
      "generated_circular_buffer_bound.lean",
      ~w(Reverse.listValueAndBound enumReverseListValue enumReverseCostBound bufferRotationSize insertCostBound insertContents)
    )

    assert bound.domain == :valid_integer_circular_buffer
    assert bound.value_model == :circular_buffer_model
    assert bound.size_measure == :capacity

    consume = {:buffer_charge, :consume}
    fill = {:buffer_charge, :fill}
    rotate = {:add, {:buffer_charge, :rotate}, rotation_surcharge(:n)}
    zero = {:buffer_charge, :zero}
    assert bound.path_bounds == %{consume: consume, fill: fill, rotate: rotate, zero: zero}
    assert bound.upper_bound == {:max, consume, {:max, fill, {:max, rotate, zero}}}

    empty = CircularBuffer.new(0)
    assert CircularBuffer.insert(empty, 1) == empty

    partial = CircularBuffer.insert(CircularBuffer.new(3), 1)
    assert %{a: [2, 1], b: [], count: 2} = CircularBuffer.insert(partial, 2)

    full = CircularBuffer.new([1, 2, 3], 3)
    assert %{a: [4], b: [2, 3], count: 3} = rotated = CircularBuffer.insert(full, 4)
    assert %{a: [5, 4], b: [3], count: 3} = CircularBuffer.insert(rotated, 5)
  end

  @tag :case_study
  test "checks the symbolic cost and rotation count of consecutive insertions" do
    assert {:ok, bound} = ReductionBounds.infer_circular_buffer_sequence_bound()

    assert_case_study(
      bound,
      {CircularBuffer, :insert, 2},
      :circular_buffer_model,
      "generated_circular_buffer_sequence_bound.lean",
      ~w(bufferObligations ReductionBounds.Periodic.eventCount ReductionBounds.Periodic.costBound
         insertManyRotationCountFrom insertManyCostBoundFrom insertManyRotationCount
         insertManyCostBound insertManyLatest)
    )

    assert bound.domain == :integer_insertions_from_empty_circular_buffer
    assert bound.size_measure == %{m: :capacity, n: :insertions}
    assert bound.value_model == :circular_buffer_sequence_model
    assert bound.periodic_rule == :constant_stride_reset
    assert %{derived: derived, supplied: []} = bound.conditions
    assert {:size_measure, :front_list_length} in derived
    assert bound.rotation_count == {:if_zero, :m, 0, {:div, {:sub, :n, 1}, :m}}

    assert bound.rotation_surcharge == rotation_surcharge(:m)

    assert bound.base_cost ==
             {:max, {:buffer_charge, :consume},
              {:max, {:buffer_charge, :fill}, {:buffer_charge, :rotate}}}

    assert bound.upper_bound ==
             {:if_zero, :m, {:mul, :n, {:buffer_charge, :zero}},
              {:add, {:mul, :n, bound.base_cost},
               {:mul, bound.rotation_count, bound.rotation_surcharge}}}

    for {capacity, insertions, expected} <- [
          {0, 0, 0},
          {0, 5, 0},
          {1, 0, 0},
          {1, 1, 0},
          {1, 5, 4},
          {3, 3, 0},
          {3, 4, 1},
          {3, 6, 1},
          {3, 7, 2},
          {3, 10, 3}
        ] do
      assert actual_rotations(capacity, insertions) == expected
    end
  end

  @tag :case_study
  test "counts rotations from reachable states and preserves FIFO contents" do
    for capacity <- 0..5 do
      empty = CircularBuffer.new(capacity)
      states = [empty | Enum.scan(1..(2 * capacity + 2), empty, &CircularBuffer.insert(&2, &1))]

      for initial <- states, insertions <- 0..(2 * capacity + 2) do
        expected =
          case capacity do
            0 -> 0
            m -> div(max(length(initial.a) + insertions - 1, 0), m)
          end

        assert check_fifo_insertions(initial, insertions) == expected,
               "rotation count for capacity #{capacity}, a length #{length(initial.a)}, " <>
                 "and #{insertions} new items"
      end
    end
  end

  test "checks input contracts for traversals and reuses a theorem in a local wrapper" do
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

    assert {:ok, %{size_measure: :input_size, value_model: :reversal}} =
             ReductionBounds.infer_list_bound({:lists, :reverse, 2}, input_contract: contract)

    assert {:ok, %{size_measure: :input_size, value_model: :composed}} =
             ReductionBounds.infer_list_bound({Fixture, :reverse_on_hit, 2}, options)

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

  defp assert_case_study(bound, target, source, file, theorems) do
    assert %{target: ^target, source: ^source, metric: :symbolic_cost} = bound

    assert [%{status: :ok, file: ^file}] =
             Enum.filter(bound.reports, &(&1.module == "Erlang.postlude"))

    assert Enum.all?(theorems, &(&1 in bound.checked_theorems))
  end

  defp member_charges() do
    {list_charge(0, :value), list_charge(1, :value), list_charge(2, :recursive_call)}
  end

  defp member_contract_upper() do
    {empty, hit, step} = member_charges()

    {:if_zero, :n, empty,
     {:max, {:add, empty, {:mul, :n, step}}, {:add, hit, {:mul, {:sub, :n, 1}, step}}}}
  end

  defp reverse_charges(), do: {list_charge(0, :value), list_charge(1, :recursive_call)}

  defp reverse_contract_upper(size) do
    {empty, step} = reverse_charges()
    {:add, empty, {:mul, size, step}}
  end

  defp list_charge(clause, operation),
    do: {:add, {:charge, clause, :dispatch}, {:charge, clause, operation}}

  defp rotation_surcharge(size) do
    {:call_bound, {Enum, :reverse, 1},
     {:add, {:buffer_charge, :enum_reverse},
      {:call_bound, {:lists, :reverse, 2}, reverse_contract_upper(size)}}}
  end

  defp actual_rotations(capacity, insertions) do
    {_, rotations} =
      Enum.reduce(1..insertions//1, {CircularBuffer.new(capacity), 0}, fn item, {buffer, count} ->
        rotates = buffer.count == capacity and buffer.b == [] and buffer.a != []
        {CircularBuffer.insert(buffer, item), count + if(rotates, do: 1, else: 0)}
      end)

    rotations
  end

  defp check_fifo_insertions(initial, insertions) do
    capacity = initial.max_size
    initial_run = {initial, CircularBuffer.to_list(initial), 0}

    {_, _, rotations} =
      Enum.reduce(1..insertions//1, initial_run, fn item, {buffer, fifo, rotations} ->
        item = -item
        next = CircularBuffer.insert(buffer, item)
        fifo = Enum.take(fifo ++ [item], -capacity)
        assert CircularBuffer.to_list(next) == fifo
        rotated = buffer.count == capacity and next.a == [item]
        {next, fifo, rotations + if(rotated, do: 1, else: 0)}
      end)

    rotations
  end

  defp contains_call_bound?({:call_bound, target, _}, target), do: true

  defp contains_call_bound?({:add, left, right}, target),
    do: contains_call_bound?(left, target) or contains_call_bound?(right, target)

  defp contains_call_bound?(_bound, _target), do: false

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

      def reverse_on_hit(key, xs) do
        if :lists.member(key, xs), do: :lists.reverse(xs, []), else: xs
      end

      def reverse_onto_on_hit(key, xs) do
        if :lists.member(key, xs), do: :lists.reverse(xs, [0]), else: xs
      end

      def reverse_via_helper(key, xs) do
        hit = :lists.member(key, xs)
        if hit, do: reverse_onto(xs), else: xs
      end

      def reverse_via_case(key, xs) do
        case :lists.member(key, xs) do
          true -> reverse_onto(xs)
          false -> xs
        end
      end

      def reverse_onto(xs), do: :lists.reverse(xs, [0])

      def reverse_twice(xs) do
        reversed = :lists.reverse(xs, [0])
        :lists.reverse(reversed, [])
      end

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
