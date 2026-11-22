namespace ReductionBounds.BoundTransfer

open ReductionBounds.IntegerAnalysis (Env bindEnv)
open ReductionBounds.IntegerCost
open ReductionBounds.CostContract (ChargesLe)

-- Only calls admitted at their actual arguments need correspondence evidence.
structure ExternalAgreement (admitted : Nat → Int → Prop)
    (smaller larger : External) : Prop where
  values : ∀ key argument, admitted key argument →
    (smaller key argument).1 = (larger key argument).1
  costs : ∀ key argument, admitted key argument →
    (smaller key argument).2 ≤ (larger key argument).2

-- This predicate covers calls in arguments, branch bodies, and recursive bodies.
inductive CallsWithin {program : Expr} {charge : Charges} {external : External}
    (admitted : Nat → Int → Prop) :
    {expr : Expr} → {env : Env} → {value : Int} → {cost : Nat} →
      Runs program charge external expr env value cost → Prop where
  | literal : CallsWithin admitted Runs.literal
  | variable : CallsWithin admitted Runs.variable
  | bind : CallsWithin admitted first → CallsWithin admitted second →
      CallsWithin admitted (Runs.bind first second)
  | binary : CallsWithin admitted first → CallsWithin admitted second →
      CallsWithin admitted (Runs.binary first second)
  | unary : CallsWithin admitted argument → CallsWithin admitted (Runs.unary argument)
  | yes : CallsWithin admitted branch → CallsWithin admitted (Runs.yes test branch)
  | no : CallsWithin admitted branch → CallsWithin admitted (Runs.no test branch)
  | call : admitted key value →
      CallsWithin admitted (argument : Runs program charge external expr env value cost) →
      CallsWithin admitted (Runs.call (key := key) argument)
  | recur : CallsWithin admitted counter → CallsWithin admitted accumulator →
      CallsWithin admitted body → CallsWithin admitted (Runs.recur counter accumulator body)

theorem compareExecution {program expr : Expr} {smaller larger : Charges}
    {smallerExternal largerExternal : External} {admitted : Nat → Int → Prop}
    {env : Env} {value : Int} {cost : Nat}
    (ordered : ChargesLe smaller larger)
    (callees : ExternalAgreement admitted smallerExternal largerExternal)
    (run : Runs program smaller smallerExternal expr env value cost)
    (covered : CallsWithin admitted run) :
    ∃ largerCost, Runs program larger largerExternal expr env value largerCost ∧
      cost ≤ largerCost := by
  induction covered with
  | literal => exact ⟨_, .literal, ordered 0 0 0⟩
  | «variable» => exact ⟨_, .variable, ordered 1 0 0⟩
  | bind _first _second firstIH secondIH =>
    obtain ⟨firstCost, firstRun, firstBound⟩ := firstIH
    obtain ⟨secondCost, secondRun, secondBound⟩ := secondIH
    exact ⟨_, .bind firstRun secondRun,
      Nat.add_le_add (Nat.add_le_add firstBound secondBound) (ordered 2 0 0)⟩
  | binary _first _second firstIH secondIH =>
    obtain ⟨firstCost, firstRun, firstBound⟩ := firstIH
    obtain ⟨secondCost, secondRun, secondBound⟩ := secondIH
    exact ⟨_, .binary firstRun secondRun,
      Nat.add_le_add (Nat.add_le_add firstBound secondBound) (ordered _ _ _)⟩
  | unary _argument ih =>
    obtain ⟨argumentCost, argumentRun, argumentBound⟩ := ih
    exact ⟨_, .unary argumentRun, Nat.add_le_add argumentBound (ordered _ _ _)⟩
  | yes _branch ih =>
    obtain ⟨branchCost, branchRun, branchBound⟩ := ih
    exact ⟨_, .yes (by assumption) branchRun, Nat.add_le_add branchBound (ordered _ _ _)⟩
  | no _branch ih =>
    obtain ⟨branchCost, branchRun, branchBound⟩ := ih
    exact ⟨_, .no (by assumption) branchRun, Nat.add_le_add branchBound (ordered _ _ _)⟩
  | call admitted _argument ih =>
    obtain ⟨argumentCost, argumentRun, argumentBound⟩ := ih
    have same := callees.values _ _ admitted
    have callBound := callees.costs _ _ admitted
    refine ⟨_, ?_, Nat.add_le_add (Nat.add_le_add argumentBound callBound) (ordered 12 0 0)⟩
    simpa only [same] using (Runs.call (external := largerExternal) argumentRun)
  | recur _counter _accumulator _body counterIH accumulatorIH bodyIH =>
    obtain ⟨counterCost, counterRun, counterBound⟩ := counterIH
    obtain ⟨accumulatorCost, accumulatorRun, accumulatorBound⟩ := accumulatorIH
    obtain ⟨bodyCost, bodyRun, bodyBound⟩ := bodyIH
    exact ⟨_, .recur counterRun accumulatorRun bodyRun,
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add counterBound accumulatorBound) bodyBound)
        (ordered 4 0 0)⟩

-- The existing semantics is deterministic for a fixed external model.
theorem runsDeterministic {program expr : Expr} {charge : Charges} {external : External}
    {env : Env} {firstValue secondValue : Int} {firstCost secondCost : Nat}
    (first : Runs program charge external expr env firstValue firstCost)
    (second : Runs program charge external expr env secondValue secondCost) :
    firstValue = secondValue ∧ firstCost = secondCost := by
  induction first generalizing secondValue secondCost with
  | literal => cases second; exact ⟨rfl, rfl⟩
  | «variable» => cases second; exact ⟨rfl, rfl⟩
  | bind _first _second firstIH secondIH =>
    cases second with
    | bind firstRun secondRun =>
      obtain ⟨rfl, rfl⟩ := firstIH firstRun
      obtain ⟨rfl, rfl⟩ := secondIH secondRun
      exact ⟨rfl, rfl⟩
  | binary _first _second firstIH secondIH =>
    cases second with
    | binary firstRun secondRun =>
      obtain ⟨rfl, rfl⟩ := firstIH firstRun
      obtain ⟨rfl, rfl⟩ := secondIH secondRun
      exact ⟨rfl, rfl⟩
  | unary _argument ih =>
    cases second with
    | unary argumentRun =>
      obtain ⟨rfl, rfl⟩ := ih argumentRun
      exact ⟨rfl, rfl⟩
  | yes test _branch ih =>
    cases second with
    | yes _ branchRun =>
      obtain ⟨rfl, rfl⟩ := ih branchRun
      exact ⟨rfl, rfl⟩
    | no failed _branchRun => simp_all
  | no test _branch ih =>
    cases second with
    | no _ branchRun =>
      obtain ⟨rfl, rfl⟩ := ih branchRun
      exact ⟨rfl, rfl⟩
    | yes passed _branchRun => simp_all
  | call _argument ih =>
    cases second with
    | call argumentRun =>
      obtain ⟨rfl, rfl⟩ := ih argumentRun
      exact ⟨rfl, rfl⟩
  | recur _counter _accumulator _body counterIH accumulatorIH bodyIH =>
    cases second with
    | recur counterRun accumulatorRun bodyRun =>
      obtain ⟨rfl, rfl⟩ := counterIH counterRun
      obtain ⟨rfl, rfl⟩ := accumulatorIH accumulatorRun
      obtain ⟨rfl, rfl⟩ := bodyIH bodyRun
      exact ⟨rfl, rfl⟩

-- The result holds for any supplied execution under the larger contract.
theorem executionCostLe {program expr : Expr} {smaller larger : Charges}
    {smallerExternal largerExternal : External} {admitted : Nat → Int → Prop}
    {env : Env} {smallerValue largerValue : Int} {smallerCost largerCost : Nat}
    (ordered : ChargesLe smaller larger)
    (callees : ExternalAgreement admitted smallerExternal largerExternal)
    (smallerRun : Runs program smaller smallerExternal expr env smallerValue smallerCost)
    (covered : CallsWithin admitted smallerRun)
    (largerRun : Runs program larger largerExternal expr env largerValue largerCost) :
    smallerValue = largerValue ∧ smallerCost ≤ largerCost := by
  obtain ⟨cost, run, bound⟩ := compareExecution ordered callees smallerRun covered
  obtain ⟨sameValue, sameCost⟩ := runsDeterministic run largerRun
  exact ⟨sameValue, sameCost ▸ bound⟩

-- Derive call-domain coverage from the existing checked size derivation.
theorem derivationCallsWithin (charge : Charges) (external : External)
    (monotone : MonotoneCharges charge) (calls : ContractsHold charge contracts external)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : ReductionBounds.IntegerAnalysis.Covers state env)
    (run : Runs program charge external expr env value cost) :
    CallsWithin (fun key argument => (contracts key).input.Holds argument) run := by
  induction derivation generalizing env value cost with
  | dead => exact False.elim covered
  | literal => cases run; exact .literal
  | «variable» => cases run; exact .variable
  | bind da db ia ib =>
    cases run with
    | bind ra rb =>
      have held := (derivationSound charge external monotone calls da covered ra).1
      exact .bind (ia covered ra)
        (ib (ReductionBounds.IntegerAnalysis.bindCovers _ _ _ _ _ covered held) rb)
  | binary da db wa wb ia ib =>
    cases run with
    | binary ra rb => exact .binary (ia covered ra) (ib covered rb)
  | unary da width ia =>
    cases run with
    | unary ra => exact .unary (ia covered ra)
  | branch width da db ia ib =>
    cases run with
    | yes test branch =>
      exact .yes (test := test)
        (ia (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered test) branch)
    | no test branch =>
      exact .no (test := test)
        (ib (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered test) branch)
  | call da pre ia =>
    cases run with
    | call ra =>
      have held := (derivationSound charge external monotone calls da covered ra).1
      exact .call (pre _ held) (ia covered ra)
  | recur da db body admitted ia ib ih =>
    cases run with
    | recur ra rb rc =>
      have ha := (derivationSound charge external monotone calls da covered ra).1
      have hb := (derivationSound charge external monotone calls db covered rb).1
      exact .recur (ia covered ra) (ib covered rb) (ih (argumentsCovered _ _ _ _ ha hb) rc)

theorem compareUnderContracts {program expr : Expr} {smaller larger : Charges}
    {smallerExternal largerExternal : External} {contracts : Contracts}
    {invariant : Int → Int → Prop} {state : ReductionBounds.IntegerAnalysis.State}
    {summary : Summary} {env : Env} {value : Int} {cost : Nat}
    (ordered : ChargesLe smaller larger) (monotone : MonotoneCharges smaller)
    (calls : ContractsHold smaller contracts smallerExternal)
    (callees : ExternalAgreement (fun key argument => (contracts key).input.Holds argument)
      smallerExternal largerExternal)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : ReductionBounds.IntegerAnalysis.Covers state env)
    (run : Runs program smaller smallerExternal expr env value cost) :
    ∃ largerCost, Runs program larger largerExternal expr env value largerCost ∧
      cost ≤ largerCost :=
  compareExecution ordered callees run
    (derivationCallsWithin smaller smallerExternal monotone calls derivation covered run)

-- Construct the smaller execution from a covered larger execution.
theorem compareFromLarger {program expr : Expr} {smaller larger : Charges}
    {smallerExternal largerExternal : External} {admitted : Nat → Int → Prop}
    {env : Env} {value : Int} {cost : Nat}
    (ordered : ChargesLe smaller larger)
    (callees : ExternalAgreement admitted smallerExternal largerExternal)
    (run : Runs program larger largerExternal expr env value cost)
    (covered : CallsWithin admitted run) :
    ∃ smallerCost, Runs program smaller smallerExternal expr env value smallerCost ∧
      smallerCost ≤ cost := by
  induction covered with
  | literal => exact ⟨_, .literal, ordered 0 0 0⟩
  | «variable» => exact ⟨_, .variable, ordered 1 0 0⟩
  | bind _first _second firstIH secondIH =>
    obtain ⟨firstCost, firstRun, firstBound⟩ := firstIH
    obtain ⟨secondCost, secondRun, secondBound⟩ := secondIH
    exact ⟨_, .bind firstRun secondRun,
      Nat.add_le_add (Nat.add_le_add firstBound secondBound) (ordered 2 0 0)⟩
  | binary _first _second firstIH secondIH =>
    obtain ⟨firstCost, firstRun, firstBound⟩ := firstIH
    obtain ⟨secondCost, secondRun, secondBound⟩ := secondIH
    exact ⟨_, .binary firstRun secondRun,
      Nat.add_le_add (Nat.add_le_add firstBound secondBound) (ordered _ _ _)⟩
  | unary _argument ih =>
    obtain ⟨argumentCost, argumentRun, argumentBound⟩ := ih
    exact ⟨_, .unary argumentRun, Nat.add_le_add argumentBound (ordered _ _ _)⟩
  | yes _branch ih =>
    obtain ⟨branchCost, branchRun, branchBound⟩ := ih
    exact ⟨_, .yes (by assumption) branchRun, Nat.add_le_add branchBound (ordered _ _ _)⟩
  | no _branch ih =>
    obtain ⟨branchCost, branchRun, branchBound⟩ := ih
    exact ⟨_, .no (by assumption) branchRun, Nat.add_le_add branchBound (ordered _ _ _)⟩
  | call admitted _argument ih =>
    obtain ⟨argumentCost, argumentRun, argumentBound⟩ := ih
    have same := callees.values _ _ admitted
    have callBound := callees.costs _ _ admitted
    refine ⟨_, ?_, Nat.add_le_add (Nat.add_le_add argumentBound callBound) (ordered 12 0 0)⟩
    simpa only [← same] using (Runs.call (external := smallerExternal) argumentRun)
  | recur _counter _accumulator _body counterIH accumulatorIH bodyIH =>
    obtain ⟨counterCost, counterRun, counterBound⟩ := counterIH
    obtain ⟨accumulatorCost, accumulatorRun, accumulatorBound⟩ := accumulatorIH
    obtain ⟨bodyCost, bodyRun, bodyBound⟩ := bodyIH
    exact ⟨_, .recur counterRun accumulatorRun bodyRun,
      Nat.add_le_add (Nat.add_le_add (Nat.add_le_add counterBound accumulatorBound) bodyBound)
        (ordered 4 0 0)⟩

-- Only the source (larger) callee budgets are assumed. Smaller budgets are
-- not assumed to cover the actual callee costs.
theorem transferDerivedBound {program expr : Expr} {smaller larger : Charges}
    {smallerExternal largerExternal : External} {contracts : Contracts}
    {invariant : Int → Int → Prop} {state : ReductionBounds.IntegerAnalysis.State}
    {summary : Summary} {env : Env} {value : Int} {cost : Nat}
    (ordered : ChargesLe smaller larger) (monotone : MonotoneCharges larger)
    (calls : ContractsHold larger contracts largerExternal)
    (callees : ExternalAgreement (fun key argument => (contracts key).input.Holds argument)
      smallerExternal largerExternal)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : ReductionBounds.IntegerAnalysis.Covers state env)
    (run : Runs program smaller smallerExternal expr env value cost) :
    ∃ sourceValue sourceCost,
      Runs program larger largerExternal expr env sourceValue sourceCost ∧
      value = sourceValue ∧ summary.size.Holds value ∧ cost ≤ sourceCost ∧
      sourceCost ≤ summary.budget.eval larger := by
  obtain ⟨sourceValue, sourceCost, sourceRun⟩ :=
    derivationTerminates larger largerExternal monotone calls derivation covered
  have within := derivationCallsWithin larger largerExternal monotone calls derivation covered sourceRun
  obtain ⟨matchedCost, matchedRun, orderedCost⟩ :=
    compareFromLarger ordered callees sourceRun within
  obtain ⟨sameValue, sameCost⟩ := runsDeterministic run matchedRun
  have sourceBound := derivationSound larger largerExternal monotone calls derivation covered sourceRun
  have valueBound : summary.size.Holds value := by
    rw [sameValue]
    exact sourceBound.1
  have costBound : cost ≤ sourceCost := by
    rw [sameCost]
    exact orderedCost
  exact ⟨sourceValue, sourceCost, sourceRun, sameValue, valueBound, costBound, sourceBound.2⟩

theorem transferBudget {program expr : Expr} {smaller larger : Charges}
    {smallerExternal largerExternal : External} {contracts : Contracts}
    {invariant : Int → Int → Prop} {state : ReductionBounds.IntegerAnalysis.State}
    {summary : Summary} {env : Env} {value : Int} {cost : Nat}
    (ordered : ChargesLe smaller larger) (monotone : MonotoneCharges larger)
    (calls : ContractsHold larger contracts largerExternal)
    (callees : ExternalAgreement (fun key argument => (contracts key).input.Holds argument)
      smallerExternal largerExternal)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : ReductionBounds.IntegerAnalysis.Covers state env)
    (run : Runs program smaller smallerExternal expr env value cost) :
    summary.size.Holds value ∧ cost ≤ summary.budget.eval larger := by
  obtain ⟨_, _, _, _, result, comparison, bound⟩ :=
    transferDerivedBound ordered monotone calls callees derivation covered run
  exact ⟨result, Nat.le_trans comparison bound⟩

theorem transferTerminates {program expr : Expr} {smaller larger : Charges}
    {smallerExternal largerExternal : External} {contracts : Contracts}
    {invariant : Int → Int → Prop} {state : ReductionBounds.IntegerAnalysis.State}
    {summary : Summary} {env : Env}
    (ordered : ChargesLe smaller larger) (monotone : MonotoneCharges larger)
    (calls : ContractsHold larger contracts largerExternal)
    (callees : ExternalAgreement (fun key argument => (contracts key).input.Holds argument)
      smallerExternal largerExternal)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : ReductionBounds.IntegerAnalysis.Covers state env) :
    ∃ value cost, Runs program smaller smallerExternal expr env value cost ∧
      summary.size.Holds value ∧ cost ≤ summary.budget.eval larger := by
  obtain ⟨value, sourceCost, sourceRun⟩ :=
    derivationTerminates larger largerExternal monotone calls derivation covered
  have within := derivationCallsWithin larger largerExternal monotone calls derivation covered sourceRun
  obtain ⟨cost, run, comparison⟩ := compareFromLarger ordered callees sourceRun within
  have bound := derivationSound larger largerExternal monotone calls derivation covered sourceRun
  exact ⟨value, cost, run, bound.1, Nat.le_trans comparison bound.2⟩

end ReductionBounds.BoundTransfer
