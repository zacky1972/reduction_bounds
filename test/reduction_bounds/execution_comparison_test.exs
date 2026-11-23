defmodule ReductionBounds.ExecutionComparisonTest do
  use ExUnit.Case, async: false

  alias ReductionBounds.{ContractComparison, CostContract, ProofInput}

  @moduletag timeout: 120_000

  test "compares bindings, arithmetic, shifts, both branches, calls, and finite recursion" do
    source = """
    namespace ExecutionExamples
    open ReductionBounds.IntegerCost
    open ReductionBounds.BoundTransfer
    open ReductionBounds.IntegerAnalysis (Env)

    def admitted (key : Nat) (argument : Int) : Prop := key = 0 ∧ 0 ≤ argument
    def externalA : External := fun _ argument => (argument + 1, 3)
    def externalB : External := fun _ argument => (argument + 1, 5)
    def emptyEnv : Env := fun _ => 0
    theorem callees : ExternalAgreement admitted externalA externalB := by
      constructor
      · intro key argument _held; rfl
      · intro key argument _held; exact (by decide : 3 ≤ 5)

    def arithmetic : ReductionBounds.IntegerCost.Expr :=
      .bind 1 (.literal 7) (.binary .add (.variable 1) (.unary .shiftLeft 2 (.literal 3)))
    theorem arithmeticRun : Runs arithmetic smallerCharges externalA arithmetic emptyEnv 19 6 := by
      exact .bind .literal (.binary .variable (.unary .literal))
    theorem arithmeticCovered : CallsWithin admitted arithmeticRun :=
      .bind .literal (.binary .variable (.unary .literal))
    example : ∃ cost, Runs arithmetic largerCharges externalB arithmetic emptyEnv 19 cost ∧ 6 ≤ cost :=
      compareExecution operationOrdering callees arithmeticRun arithmeticCovered

    theorem noCalls : ExternalAgreement (fun _ _ => False) externalA externalB := by
      constructor
      · intro key argument impossible; exact False.elim impossible
      · intro key argument impossible; exact False.elim impossible
    example : ∃ cost, Runs arithmetic largerCharges externalB arithmetic emptyEnv 19 cost ∧ 6 ≤ cost :=
      compareExecution operationOrdering noCalls arithmeticRun
        (.bind .literal (.binary .variable (.unary .literal)))

    def yesBranch : ReductionBounds.IntegerCost.Expr := .branch .lt 0 1 (.literal 7) (.literal 9)
    theorem yesRun : Runs yesBranch smallerCharges externalA yesBranch emptyEnv 7 2 :=
      .yes (by decide) .literal
    example : ∃ cost, Runs yesBranch largerCharges externalB yesBranch emptyEnv 7 cost ∧ 2 ≤ cost :=
      compareExecution operationOrdering callees yesRun (.yes (test := by decide) .literal)

    def noBranch : ReductionBounds.IntegerCost.Expr := .branch .gt 0 1 (.literal 7) (.literal 9)
    theorem noRun : Runs noBranch smallerCharges externalA noBranch emptyEnv 9 2 :=
      .no (by decide) .literal
    example : ∃ cost, Runs noBranch largerCharges externalB noBranch emptyEnv 9 cost ∧ 2 ≤ cost :=
      compareExecution operationOrdering callees noRun (.no (test := by decide) .literal)

    def callProgram : ReductionBounds.IntegerCost.Expr := .call 0 (.literal 7)
    theorem callRunA : Runs callProgram smallerCharges externalA callProgram emptyEnv 8 5 :=
      .call .literal
    theorem callRunB : Runs callProgram largerCharges externalB callProgram emptyEnv 8 9 :=
      .call .literal
    example : (8 : Int) = 8 ∧ (5 : Nat) ≤ 9 :=
      executionCostLe operationOrdering callees callRunA
        (.call (by unfold admitted; decide) .literal) callRunB

    def recursiveProgram : ReductionBounds.IntegerCost.Expr := .branch .le 0 0 (.variable 1)
      (.recur (.binary .subtract (.variable 0) (.literal 1))
        (.binary .add (.variable 1) (.variable 0)))
    def initialEnv : Env := fun index => if index = 0 then 1 else 0
    theorem recursiveRun : Runs recursiveProgram smallerCharges externalA
        recursiveProgram initialEnv 1 10 := by
      exact .no (by decide)
        (.recur (.binary .variable .literal) (.binary .variable .variable)
          (.yes (by decide) .variable))
    theorem recursiveCovered : CallsWithin admitted recursiveRun :=
      .no (test := by decide)
        (.recur (.binary .variable .literal) (.binary .variable .variable)
          (.yes (test := by decide) .variable))
    example : ∃ cost, Runs recursiveProgram largerCharges externalB
        recursiveProgram initialEnv 1 cost ∧ 10 ≤ cost :=
      compareExecution operationOrdering callees recursiveRun recursiveCovered

    end ExecutionExamples
    """

    reports = verify(source)
    assert reports != []
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  test "checks operation indexes against the integer execution semantics" do
    source = """
    example : smallerCharges 0 0 0 = 1 := by decide
    example : smallerCharges 1 0 0 = 2 := by decide
    example : smallerCharges 2 0 0 = 3 := by decide
    example : smallerCharges 3 0 0 = 4 := by decide
    example : smallerCharges 4 0 0 = 5 := by decide
    example : smallerCharges 5 0 0 = 6 := by decide
    example : smallerCharges 6 0 0 = 7 := by decide
    example : smallerCharges 7 0 0 = 8 := by decide
    example : smallerCharges 8 0 0 = 9 := by decide
    example : smallerCharges 9 0 0 = 10 := by decide
    example : smallerCharges 10 0 0 = 11 := by decide
    example : smallerCharges 11 0 0 = 12 := by decide
    example : smallerCharges 12 0 0 = 13 := by decide
    """

    operations = CostContract.execution_operations()
    smaller = operations |> Enum.with_index(1) |> Map.new()
    larger = Map.new(smaller, fn {name, cost} -> {name, cost + 1} end)
    reports = verify(source, smaller, larger)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  test "derives call coverage from the existing size derivation and input conditions" do
    source = """
    open ReductionBounds.IntegerCost
    open ReductionBounds.BoundTransfer
    open ReductionBounds.IntegerSize
    def callContracts : Contracts := fun _ =>
      ⟨.bounded {}, .bounded {}, .item 0 0 0⟩
    def external : External := fun _ argument => (argument, 0)
    def program : ReductionBounds.IntegerCost.Expr := .call 0 (.literal 7)
    def state : ReductionBounds.IntegerAnalysis.State := some (fun _ => .bounded {})
    theorem callConditions : ContractsHold smallerCharges callContracts external := by
      intro key argument _input
      exact ⟨unconstrained argument, Nat.zero_le _⟩
    theorem derivation : Derives program callContracts (fun _ _ => True) state program
        ⟨.bounded {}, .add (.add (.item 0 0 0) (.item 0 0 0)) (.item 12 0 0)⟩ :=
      .call .literal (by intro value _held; exact unconstrained value)
    theorem initialCovered : ReductionBounds.IntegerAnalysis.Covers state (fun _ => 0) :=
      fun _ => unconstrained 0
    theorem exampleRun : Runs program smallerCharges external program (fun _ => 0) 7 2 :=
      .call .literal
    theorem sameCallees : ExternalAgreement
        (fun key argument => (callContracts key).input.Holds argument) external external := by
      constructor
      · intro key argument _held; rfl
      · intro key argument _held; exact Nat.le_refl _
    example : ∃ cost, Runs program largerCharges external program (fun _ => 0) 7 cost ∧ 2 ≤ cost :=
      compareUnderContracts operationOrdering smallerMonotone callConditions sameCallees
        derivation initialCovered exampleRun
    """

    reports = verify(source)
    assert Enum.all?(reports, &(&1.status == :ok)), inspect(reports, limit: :infinity)
  end

  test "rejects changed callee values even when their costs are ordered" do
    source = """
    open ReductionBounds.BoundTransfer
    example : ExternalAgreement (fun _ _ => True)
        (fun _ argument => (argument + 1, 3)) (fun _ argument => (argument + 2, 5)) := by
      constructor
      · intro key argument _held; rfl
      · intro key argument _held; exact (by decide : 3 ≤ 5)
    """

    assert Enum.any?(verify(source), &(&1.status == :error))
  end

  test "ordered callee budgets do not imply ordered actual callee costs" do
    source = """
    open ReductionBounds.BoundTransfer
    example : (9 : Nat) ≤ 10 ∧ (1 : Nat) ≤ 20 ∧ (10 : Nat) ≤ 20 := by decide
    example : ExternalAgreement (fun _ _ => True)
        (fun _ argument => (argument, 9)) (fun _ argument => (argument, 1)) := by
      constructor
      · intro key argument _held; rfl
      · intro key argument _held; exact (by decide : 9 ≤ 1)
    """

    assert Enum.any?(verify(source), &(&1.status == :error))
  end

  test "rejects a nested call when only its initial argument meets the admitted domain" do
    source = """
    open ReductionBounds.IntegerCost
    open ReductionBounds.BoundTransfer
    def external : External := fun _ argument => (argument + 1, 0)
    def callRun : Runs (.literal 0) smallerCharges external (.call 0 (.call 0 (.literal 7)))
        (fun _ => 0) 9 3 := .call (.call .literal)
    example : CallsWithin (fun _ argument => argument ≤ 7) callRun :=
      .call (by decide) (.call (by decide) .literal)
    """

    assert Enum.any?(verify(source), &(&1.status == :error))
  end

  defp verify(source, smaller \\ nil, larger \\ nil) do
    smaller = smaller || Map.new(CostContract.operations(), &{&1, 1})
    larger = larger || Map.new(CostContract.operations(), &{&1, 2})
    {:ok, a} = CostContract.new(id: :a, functions: smaller)
    {:ok, b} = CostContract.new(id: :b, functions: larger)
    {:ok, candidate, proof} = ContractComparison.infer(a, b)
    proof = %{proof | source: proof.source <> "\n" <> source}
    {proof, _evidence} = ProofInput.audit_bound(proof, candidate)
    {:ok, postludes} = ProofInput.contract_postludes(proof)
    translation = Lynx.Translation.new(postludes: postludes)
    ReductionBounds.Verification.verify!(translation)
  end
end
