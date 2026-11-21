namespace ReductionBounds.IntegerCost
open ReductionBounds.IntegerSize
open ReductionBounds.IntegerAnalysis (Env State Covers bindEnv bindState refineState Binary Unary)

abbrev Charges := Nat → Nat → Nat → Nat

def MonotoneCharges (charge : Charges) : Prop :=
  ∀ operation a b x y, a ≤ x → b ≤ y → charge operation a b ≤ charge operation x y

inductive Budget where
  | zero
  | item (operation leftBits rightBits : Nat)
  | add (left right : Budget)
  | max (left right : Budget)
  deriving DecidableEq

def Budget.eval (charge : Charges) : Budget → Nat
  | .zero => 0
  | .item operation a b => charge operation a b
  | .add a b => a.eval charge + b.eval charge
  | .max a b => Nat.max (a.eval charge) (b.eval charge)

def binaryId : Binary → Nat
  | .add => 5 | .subtract => 6 | .multiply => 7 | .bitXor => 8

def unaryId : Unary → Nat
  | .shiftLeft => 9 | .shiftRight => 10 | .mask => 11

inductive Expr where
  | literal (value : Int)
  | variable (index : Nat)
  | bind (index : Nat) (rhs body : Expr)
  | binary (operation : Binary) (left right : Expr)
  | unary (operation : Unary) (amount : Nat) (value : Expr)
  | branch (comparison : Comparison) (index : Nat) (constant : Int) (yes no : Expr)
  | call (key : Nat) (argument : Expr)
  | recur (counter accumulator : Expr)
  deriving DecidableEq

structure Contract where
  input : Domain
  output : Domain
  budget : Budget
  deriving DecidableEq

abbrev Contracts := Nat → Contract
abbrev External := Nat → Int → Int × Nat

def ContractsHold (charge : Charges) (contracts : Contracts) (external : External) : Prop :=
  ∀ key value, (contracts key).input.Holds value →
    (contracts key).output.Holds (external key value).1 ∧
      (external key value).2 ≤ (contracts key).budget.eval charge

-- External functions denote normally returning calls under their contracts.
inductive Runs (program : Expr) (charge : Charges) (external : External) : Expr → Env → Int → Nat → Prop where
  | literal : Runs program charge external (.literal value) env value (charge 0 0 0)
  | variable : Runs program charge external (.variable index) env (env index) (charge 1 0 0)
  | bind : Runs program charge external rhs env value first →
      Runs program charge external body (bindEnv env index value) result second →
      Runs program charge external (.bind index rhs body) env result (first + second + charge 2 0 0)
  | binary : Runs program charge external left env a ca → Runs program charge external right env b cb →
      Runs program charge external (.binary operation left right) env (operation.eval a b)
        (ca + cb + charge (binaryId operation) (magnitudeBits a) (magnitudeBits b))
  | unary : Runs program charge external value env a ca →
      Runs program charge external (.unary operation amount value) env (operation.eval amount a)
        (ca + charge (unaryId operation) (magnitudeBits a) amount)
  | yes : comparison.test (env index) constant = true → Runs program charge external yes env value cost →
      Runs program charge external (.branch comparison index constant yes no) env value
        (cost + charge 3 (magnitudeBits (env index)) (magnitudeBits constant))
  | no : comparison.test (env index) constant = false → Runs program charge external no env value cost →
      Runs program charge external (.branch comparison index constant yes no) env value
        (cost + charge 3 (magnitudeBits (env index)) (magnitudeBits constant))
  | call : Runs program charge external argument env value cost →
      Runs program charge external (.call key argument) env (external key value).1
        (cost + (external key value).2 + charge 12 0 0)
  | recur : Runs program charge external counter env a ca → Runs program charge external accumulator env b cb →
      Runs program charge external program (fun index => if index = 0 then a else if index = 1 then b else 0) value cost →
      Runs program charge external (.recur counter accumulator) env value (ca + cb + cost + charge 4 0 0)

inductive RunInvariant {program : Expr} {charge : Charges} {external : External}
    (invariant : Int → Int → Prop) :
    {expr : Expr} → {env : Env} → {value : Int} → {cost : Nat} →
      Runs program charge external expr env value cost → Prop where
  | literal : RunInvariant invariant Runs.literal
  | variable : RunInvariant invariant Runs.variable
  | bind : RunInvariant invariant rleft → RunInvariant invariant rright →
      RunInvariant invariant (Runs.bind rleft rright)
  | binary : RunInvariant invariant rleft → RunInvariant invariant rright →
      RunInvariant invariant (Runs.binary rleft rright)
  | unary : RunInvariant invariant rarg → RunInvariant invariant (Runs.unary rarg)
  | yes : RunInvariant invariant rbranch → RunInvariant invariant (Runs.yes test rbranch)
  | no : RunInvariant invariant rbranch → RunInvariant invariant (Runs.no test rbranch)
  | call : RunInvariant invariant rarg → RunInvariant invariant (Runs.call rarg)
  | recur : invariant a b →
      RunInvariant invariant (rleft : Runs program charge external counter env a ca) →
      RunInvariant invariant (rright : Runs program charge external accumulator env b cb) →
      RunInvariant invariant rbody → RunInvariant invariant (Runs.recur rleft rright rbody)

def lookup (state : State) (index : Nat) : Domain :=
  match state with | none => .unreachable | some sizes => sizes index

def argumentState (a b : Domain) : State :=
  match a.normalize, b.normalize with
  | .bounded left, .bounded right => some (fun index => if index = 0 then .bounded left
      else if index = 1 then .bounded right else .bounded {})
  | _, _ => none

theorem argumentsCovered (a b : Domain) (x y : Int) (ha : a.Holds x) (hb : b.Holds y) :
    Covers (argumentState a b) (fun index => if index = 0 then x else if index = 1 then y else 0) := by
  have left := (normalizeSound a x).mpr ha
  have right := (normalizeSound b y).mpr hb
  cases ac : a.normalize with
  | unreachable => simp [ac, Domain.Holds] at left
  | bounded aa =>
    cases bc : b.normalize with
    | unreachable => simp [bc, Domain.Holds] at right
    | bounded bb =>
      simp only [argumentState, ac, bc, Covers]
      intro index
      by_cases zero : index = 0
      · simpa [ac, zero] using left
      · by_cases one : index = 1
        · simpa [bc, zero, one] using right
        · simpa [zero, one, Domain.Holds] using unconstrained 0

def Width (size : Domain) (width : Nat) : Prop :=
  ∀ value, size.Holds value → magnitudeBits value ≤ width

theorem knownWidth (bounds : Bounds) (width : Nat) (known : bounds.magnitudeBits = some width) :
    Width (.bounded bounds) width := by
  intro value held
  exact magnitudeBitsMinimal value width (magnitudeBound bounds value width held known)

def lowerIncludes : Option Int → Option Int → Bool
  | none, _ => true
  | some _, none => false
  | some required, some actual => decide (required ≤ actual)

def upperIncludes : Option Int → Option Int → Bool
  | none, _ => true
  | some _, none => false
  | some required, some actual => decide (actual ≤ required)

def bitsInclude : Option Nat → Option Nat → Bool
  | none, _ => true
  | some _, none => false
  | some required, some actual => decide (actual ≤ required)

def included (actual required : Domain) : Bool :=
  match actual.normalize, required.normalize with
  | .unreachable, _ => true
  | _, .unreachable => false
  | .bounded a, .bounded b => lowerIncludes b.lower a.lower &&
      upperIncludes b.upper a.upper && bitsInclude b.magnitudeBits a.magnitudeBits

theorem inclusionSound (actual required : Domain) (accepted : included actual required = true) :
    ∀ value, actual.Holds value → required.Holds value := by
  intro value held
  have h := (normalizeSound actual value).mpr held
  apply (normalizeSound required value).mp
  cases ac : actual.normalize with
  | unreachable => simp [ac, Domain.Holds] at h
  | bounded a =>
    cases rc : required.normalize with
    | unreachable => simp [included, ac, rc] at accepted
    | bounded b =>
      simp only [included, ac, rc, Bool.and_eq_true] at accepted
      rcases accepted with ⟨⟨lo, hi⟩, bits⟩
      simp only [ac, Domain.Holds] at h
      simp only [Domain.Holds]
      rcases h with ⟨hl, hu, hw⟩
      refine ⟨?_, ?_, ?_⟩
      · cases bl : b.lower <;> cases al : a.lower <;>
          simp_all [lowerIncludes, LowerHolds] <;> omega
      · cases bu : b.upper <;> cases au : a.upper <;>
          simp_all [upperIncludes, UpperHolds] <;> omega
      · cases bw : b.magnitudeBits with
        | none => trivial
        | some width =>
          cases aw : a.magnitudeBits with
          | none => simp [bitsInclude, bw, aw] at bits
          | some small =>
            have order : small ≤ width := by simpa [bitsInclude, bw, aw] using bits
            have cap := Nat.pow_le_pow_right (n := 2) (by decide) order
            have smallBound : value.natAbs < 2 ^ small := by simpa [MagnitudeHolds, aw] using hw
            exact Nat.lt_of_lt_of_le smallBound cap

theorem lookupCovered (state : State) (env : Env) (index : Nat) (covered : Covers state env) :
    (lookup state index).Holds (env index) := by
  cases state with
  | none => exact False.elim covered
  | some sizes => exact covered index

structure Summary where
  size : Domain
  budget : Budget
  deriving DecidableEq

-- A finite derivation tree covers every branch, including recursive calls.
inductive Derives (program : Expr) (contracts : Contracts) (invariant : Int → Int → Prop) : State → Expr → Summary → Prop where
  | dead : Derives program contracts invariant none expr ⟨.unreachable, .zero⟩
  | literal : Derives program contracts invariant state (.literal value) ⟨.bounded (singleton value), .item 0 0 0⟩
  | variable : Derives program contracts invariant state (.variable index) ⟨lookup state index, .item 1 0 0⟩
  | bind : Derives program contracts invariant state rhs a →
      Derives program contracts invariant (bindState state index a.size) body b →
      Derives program contracts invariant state (.bind index rhs body)
        ⟨b.size, .add (.add a.budget b.budget) (.item 2 0 0)⟩
  | binary : Derives program contracts invariant state left a → Derives program contracts invariant state right b →
      Width a.size wa → Width b.size wb →
      Derives program contracts invariant state (.binary operation left right)
        ⟨operation.infer a.size b.size, .add (.add a.budget b.budget) (.item (binaryId operation) wa wb)⟩
  | unary : Derives program contracts invariant state value a → Width a.size width →
      Derives program contracts invariant state (.unary operation amount value)
        ⟨operation.infer amount a.size, .add a.budget (.item (unaryId operation) width amount)⟩
  | branch : Width (lookup state index) width →
      Derives program contracts invariant (refineState state comparison index constant true) yes a →
      Derives program contracts invariant (refineState state comparison index constant false) no b →
      Derives program contracts invariant state (.branch comparison index constant yes no)
        ⟨a.size.join b.size, .add (.max a.budget b.budget) (.item 3 width (magnitudeBits constant))⟩
  | call : Derives program contracts invariant state argument a →
      (∀ value, a.size.Holds value → (contracts key).input.Holds value) →
      Derives program contracts invariant state (.call key argument)
        ⟨(contracts key).output, .add (.add a.budget (contracts key).budget) (.item 12 0 0)⟩
  | recur : Derives program contracts invariant state counter a → Derives program contracts invariant state accumulator b →
      Derives program contracts invariant (argumentState a.size b.size) program result →
      (∀ x y, a.size.Holds x → b.size.Holds y → invariant x y) →
      Derives program contracts invariant state (.recur counter accumulator)
        ⟨result.size, .add (.add (.add a.budget b.budget) result.budget) (.item 4 0 0)⟩

-- Cost safety quantifies over every finite execution under the call contracts.
theorem derivationSound (charge : Charges) (external : External) (monotone : MonotoneCharges charge)
    (calls : ContractsHold charge contracts external)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : Covers state env) (run : Runs program charge external expr env value cost) :
    summary.size.Holds value ∧ cost ≤ summary.budget.eval charge := by
  induction derivation generalizing env value cost with
  | dead => exact False.elim covered
  | literal =>
    cases run
    exact ⟨(singletonExact _ _).mpr rfl, Nat.le_refl _⟩
  | «variable» =>
    cases run
    exact ⟨lookupCovered _ _ _ covered, Nat.le_refl _⟩
  | bind da db ia ib =>
    cases run with
    | bind ra rb =>
      obtain ⟨ha, ca⟩ := ia covered ra
      obtain ⟨hb, cb⟩ := ib (ReductionBounds.IntegerAnalysis.bindCovers _ _ _ _ _ covered ha) rb
      exact ⟨hb, Nat.add_le_add_right (Nat.add_le_add ca cb) _⟩
  | binary da db wa wb ia ib =>
    cases run with
    | binary ra rb =>
      obtain ⟨ha, ca⟩ := ia covered ra
      obtain ⟨hb, cb⟩ := ib covered rb
      exact ⟨ReductionBounds.IntegerAnalysis.binarySound _ _ _ _ _ ha hb,
        Nat.add_le_add (Nat.add_le_add ca cb) (monotone _ _ _ _ _ (wa _ ha) (wb _ hb))⟩
  | unary da width ia =>
    cases run with
    | unary ra =>
      obtain ⟨ha, ca⟩ := ia covered ra
      exact ⟨ReductionBounds.IntegerAnalysis.unarySound _ _ _ _ ha,
        Nat.add_le_add ca (monotone _ _ _ _ _ (width _ ha) (Nat.le_refl _))⟩
  | @branch state index bound comparison constant yes a no b width da db ia ib =>
    have variableHeld := lookupCovered state env index covered
    cases run with
    | yes test branch =>
      obtain ⟨held, bound⟩ := ia (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered test) branch
      exact ⟨joinLeftSound _ _ _ held, Nat.add_le_add (Nat.le_trans bound (Nat.le_max_left _ _))
        (monotone _ _ _ _ _ (width _ variableHeld) (Nat.le_refl _))⟩
    | no test branch =>
      obtain ⟨held, bound⟩ := ib (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered test) branch
      exact ⟨joinRightSound _ _ _ held, Nat.add_le_add (Nat.le_trans bound (Nat.le_max_right _ _))
        (monotone _ _ _ _ _ (width _ variableHeld) (Nat.le_refl _))⟩
  | call da pre ia =>
    cases run with
    | call argument =>
      obtain ⟨held, bound⟩ := ia covered argument
      obtain ⟨result, extra⟩ := calls _ _ (pre _ held)
      exact ⟨result, Nat.add_le_add_right (Nat.add_le_add bound extra) _⟩
  | recur da db body admitted ia ib ih =>
    cases run with
    | recur ra rb call =>
      obtain ⟨ha, ca⟩ := ia covered ra
      obtain ⟨hb, cb⟩ := ib covered rb
      obtain ⟨held, bound⟩ := ih (argumentsCovered _ _ _ _ ha hb) call
      exact ⟨held, Nat.add_le_add_right (Nat.add_le_add (Nat.add_le_add ca cb) bound) _⟩

theorem derivationInvariant (charge : Charges) (external : External) (monotone : MonotoneCharges charge)
    (calls : ContractsHold charge contracts external)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : Covers state env) (run : Runs program charge external expr env value cost) :
    RunInvariant invariant run := by
  induction derivation generalizing env value cost with
  | dead => exact False.elim covered
  | literal => cases run; exact .literal
  | «variable» => cases run; exact .variable
  | bind da db ia ib =>
    cases run with
    | bind ra rb =>
      have held := (derivationSound charge external monotone calls da covered ra).1
      exact .bind (ia covered ra) (ib (ReductionBounds.IntegerAnalysis.bindCovers _ _ _ _ _ covered held) rb)
  | binary da db wa wb ia ib =>
    cases run with
    | binary ra rb => exact .binary (ia covered ra) (ib covered rb)
  | unary da width ia =>
    cases run with
    | unary ra => exact .unary (ia covered ra)
  | branch width da db ia ib =>
    cases run with
    | yes test run => exact .yes (test := test) (ia (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered test) run)
    | no test run => exact .no (test := test) (ib (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered test) run)
  | call da pre ia =>
    cases run with
    | call ra => exact .call (ia covered ra)
  | recur da db body admitted ia ib ih =>
    cases run with
    | recur ra rb rc =>
      have ha := (derivationSound charge external monotone calls da covered ra).1
      have hb := (derivationSound charge external monotone calls db covered rb).1
      exact .recur (admitted _ _ ha hb) (ia covered ra) (ib covered rb) (ih (argumentsCovered _ _ _ _ ha hb) rc)

-- A finite checked derivation also constructs a normal finite execution.
theorem derivationTerminates (charge : Charges) (external : External) (monotone : MonotoneCharges charge)
    (calls : ContractsHold charge contracts external)
    (derivation : Derives program contracts invariant state expr summary)
    (covered : Covers state env) :
    ∃ value cost, Runs program charge external expr env value cost := by
  induction derivation generalizing env with
  | dead => exact False.elim covered
  | literal => exact ⟨_, _, .literal⟩
  | «variable» => exact ⟨_, _, .variable⟩
  | bind da db ia ib =>
    obtain ⟨value, cost, first⟩ := ia covered
    have held := (derivationSound charge external monotone calls da covered first).1
    obtain ⟨result, secondCost, second⟩ := ib (ReductionBounds.IntegerAnalysis.bindCovers _ _ _ _ _ covered held)
    exact ⟨_, _, .bind first second⟩
  | binary da db wa wb ia ib =>
    obtain ⟨a, ca, ra⟩ := ia covered
    obtain ⟨b, cb, rb⟩ := ib covered
    exact ⟨_, _, .binary ra rb⟩
  | unary da width ia =>
    obtain ⟨a, ca, ra⟩ := ia covered
    exact ⟨_, _, .unary ra⟩
  | @branch state index bound comparison constant yes a no b width da db ia ib =>
    by_cases test : comparison.test (env index) constant = true
    · obtain ⟨value, cost, run⟩ := ia (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered test)
      exact ⟨_, _, .yes test run⟩
    · have failed : comparison.test (env index) constant = false := by simp [test]
      obtain ⟨value, cost, run⟩ := ib (ReductionBounds.IntegerAnalysis.refineCovers _ _ _ _ _ _ covered failed)
      exact ⟨_, _, .no failed run⟩
  | call da pre ia =>
    obtain ⟨value, cost, run⟩ := ia covered
    exact ⟨_, _, .call run⟩
  | recur da db body admitted ia ib ih =>
    obtain ⟨a, ca, ra⟩ := ia covered
    obtain ⟨b, cb, rb⟩ := ib covered
    have ha := (derivationSound charge external monotone calls da covered ra).1
    have hb := (derivationSound charge external monotone calls db covered rb).1
    obtain ⟨value, cost, run⟩ := ih (argumentsCovered _ _ _ _ ha hb)
    exact ⟨_, _, .recur ra rb run⟩

end ReductionBounds.IntegerCost
