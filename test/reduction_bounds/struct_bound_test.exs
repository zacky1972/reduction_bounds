defmodule ReductionBounds.StructBoundTest do
  use ExUnit.Case, async: true
  @moduletag timeout: 300_000

  alias ReductionBounds.{CoreFragment, ProofInput, SearchBound, TestFixtures}
  alias ReductionBounds.Fixtures.BoundedCounter

  setup_all do
    {BoundedCounter, beam} = TestFixtures.bounded_counter()
    %{beam: beam}
  end

  test "checks a cost bound for the guarded debit and preserves opaque paths", %{beam: beam} do
    target = {BoundedCounter, :debit, 2}

    assert {:ok,
            %{
              target: ^target,
              metric: :symbolic_cost,
              value_agreement: :unsupported,
              upper_bound: upper_bound,
              opaque_paths: [_, _] = opaque_paths,
              normalization: %{certificates: [], program: %{expression: expression}},
              reports: reports
            }} = ReductionBounds.infer_struct_bound(target, beam_binaries: [beam])

    assert_verified(reports)
    assert {:case_map_guarded, _, _, _, _, _} = expression
    charges = charges(upper_bound)

    for operation <- [:map_match, :branch, :is_integer, :ge, :sub, :is_map, :update] do
      assert {:operation_cost, operation} in charges
    end

    for id <- opaque_paths, do: assert({:opaque_cost, id} in charges)
  end

  test "composes a bound for a different field with the same rules", %{beam: beam} do
    assert {:ok, %{upper_bound: upper_bound, reports: reports}} =
             ReductionBounds.infer_struct_bound({BoundedCounter, :set_limit, 2},
               beam_binaries: [beam]
             )

    assert_verified(reports)
    charges = charges(upper_bound)
    assert {:operation_cost, :update} in charges
    refute {:operation_cost, :sub} in charges
  end

  test "proves value agreement from extracted Core while bounding the original operation", %{
    beam: beam
  } do
    assert {:ok,
            %{
              upper_bound: upper_bound,
              value_agreement: :checked,
              normalization: %{certificates: [%{path: [:matched, :body], normalized: read}]},
              reports: reports
            }} =
             ReductionBounds.infer_struct_bound({BoundedCounter, :read_checked, 1},
               beam_binaries: [beam]
             )

    assert_verified(reports)
    assert {:field, _, "balance"} = read
    assert {:operation_cost, :map_match} in charges(upper_bound)
    refute {:operation_cost, :field} in charges(upper_bound)
  end

  test "Lean evaluates the decoded debit clauses under the model", %{beam: beam} do
    assert {:ok, core} = SearchBound.core_function({BoundedCounter, :debit, 2}, [beam])
    assert {:ok, %{expression: expression}} = CoreFragment.decode(core)

    proof = %Lynx.Lean{
      file: "debit_examples.lean",
      span: {1, 1},
      indentation: 0,
      source: debit_examples(expression)
    }

    assert {:ok, postludes} = ProofInput.postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)

    reports =
      ReductionBounds.Verification.verify!(translation,
        postlude_imports: ["Erlang.erlang", "Erlang.maps"]
      )

    assert_verified(reports)
  end

  defp assert_verified(reports) do
    assert Enum.all?(reports, &(&1.status == :ok))
    assert List.last(reports).module == "Erlang.postlude"
  end

  defp charges({operation, left, right}) when operation in [:add, :max],
    do: charges(left) ++ charges(right)

  defp charges(cost), do: [cost]

  defp debit_examples(expression) do
    """
    namespace ReductionBounds.Core

    def debitExample : Expr := #{ProofInput.expression(expression)}

    def initialCounter : Lynx.Term :=
      .map [(.atom "__struct__", .atom "Elixir.ReductionBounds.Fixtures.BoundedCounter"),
            (.atom "balance", .integer 10), (.atom "limit", .integer 20)]

    def debitEnv (counter amount : Lynx.Term) : Env :=
      fun name => if name = "integer:0" then some counter
        else if name = "integer:1" then some amount else none

    def runDebit (counter amount : Lynx.Term) : Result :=
      eval (fun _ _ => none) (debitEnv counter amount) debitExample

    def fieldAfter (key : String) (amount : Lynx.Term) : Option Lynx.Term :=
      match runDebit initialCounter amount with
      | some (.ok (.map entries)) => fieldLookup entries key
      | _ => none

    example : fieldAfter "balance" (.integer 4) = some (.integer 6) := by rfl
    example : fieldAfter "balance" (.integer 10) = some (.integer 0) := by rfl
    example : fieldAfter "limit" (.integer 4) = some (.integer 20) := by rfl
    example : runDebit initialCounter (.integer (-1)) = some (.ok initialCounter) := by rfl
    example : runDebit initialCounter (.integer 11) = some (.ok initialCounter) := by rfl
    example : runDebit initialCounter (.atom "bad") = some (.ok initialCounter) := by rfl
    example : runDebit (.atom "bad") (.integer 1) = none := by rfl

    end ReductionBounds.Core
    """
  end
end
