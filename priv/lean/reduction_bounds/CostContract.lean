namespace ReductionBounds.CostContract

inductive Expr where
  | constant (value : Nat)
  | left
  | right
  | add (a b : Expr)
  | mul (a b : Expr)
  | max (a b : Expr)
  deriving DecidableEq

def Expr.eval (left right : Nat) : Expr → Nat
  | .constant value => value
  | .left => left
  | .right => right
  | .add a b => a.eval left right + b.eval left right
  | .mul a b => a.eval left right * b.eval left right
  | .max a b => Nat.max (a.eval left right) (b.eval left right)

theorem Expr.monotone (expr : Expr) (a b x y : Nat) (ha : a ≤ x) (hb : b ≤ y) :
    expr.eval a b ≤ expr.eval x y := by
  induction expr with
  | constant _value => exact Nat.le_refl _
  | left => exact ha
  | right => exact hb
  | add _left _right leftIH rightIH => exact Nat.add_le_add leftIH rightIH
  | mul _left _right leftIH rightIH => exact Nat.mul_le_mul leftIH rightIH
  | max _left _right leftIH rightIH =>
    exact Nat.max_le.mpr
      ⟨Nat.le_trans leftIH (Nat.le_max_left _ _),
       Nat.le_trans rightIH (Nat.le_max_right _ _)⟩

-- A certificate establishes a universal inequality, not sampled comparisons.
inductive ExprLe : Expr → Expr → Prop where
  | refl {expr} : ExprLe expr expr
  | zero {expr} : ExprLe (.constant 0) expr
  | constant {a b} : a ≤ b → ExprLe (.constant a) (.constant b)
  | add {a b c d} : ExprLe a c → ExprLe b d → ExprLe (.add a b) (.add c d)
  | mul {a b c d} : ExprLe a c → ExprLe b d → ExprLe (.mul a b) (.mul c d)
  | max {a b c d} : ExprLe a c → ExprLe b d → ExprLe (.max a b) (.max c d)
  | addLeft {a b c} : ExprLe a b → ExprLe a (.add b c)
  | addRight {a b c} : ExprLe a c → ExprLe a (.add b c)
  | maxLeft {a b c} : ExprLe a b → ExprLe a (.max b c)
  | maxRight {a b c} : ExprLe a c → ExprLe a (.max b c)
  | maxCases {a b c} : ExprLe a c → ExprLe b c → ExprLe (.max a b) c

theorem ExprLe.sound {lhs rhs : Expr} (proof : ExprLe lhs rhs) (a b : Nat) :
    lhs.eval a b ≤ rhs.eval a b := by
  induction proof with
  | refl => exact Nat.le_refl _
  | zero => exact Nat.zero_le _
  | constant bound => exact bound
  | add _first _second firstIH secondIH => exact Nat.add_le_add firstIH secondIH
  | mul _first _second firstIH secondIH => exact Nat.mul_le_mul firstIH secondIH
  | max _first _second firstIH secondIH =>
    exact Nat.max_le.mpr
      ⟨Nat.le_trans firstIH (Nat.le_max_left _ _),
       Nat.le_trans secondIH (Nat.le_max_right _ _)⟩
  | addLeft _inner ih =>
    simp only [Expr.eval]
    omega
  | addRight _inner ih =>
    simp only [Expr.eval]
    omega
  | maxLeft _inner ih =>
    exact Nat.le_trans ih (Nat.le_max_left _ _)
  | maxRight _inner ih =>
    exact Nat.le_trans ih (Nat.le_max_right _ _)
  | maxCases _first _second firstIH secondIH =>
    exact Nat.max_le.mpr ⟨firstIH, secondIH⟩

def charges : List Expr → ReductionBounds.IntegerCost.Charges
  | [], _, _, _ => 0
  | expr :: _, 0, left, right => expr.eval left right
  | _ :: rest, index + 1, left, right => charges rest index left right

abbrev ChargesLe (smaller larger : ReductionBounds.IntegerCost.Charges) : Prop :=
  ∀ operation left right, smaller operation left right ≤ larger operation left right

theorem functionsMonotone (definitions : List Expr) :
    ReductionBounds.IntegerCost.MonotoneCharges (charges definitions) := by
  induction definitions with
  | nil =>
    intro _ _ _ _ _ _ _
    exact Nat.le_refl _
  | cons expr _rest ih =>
    intro operation a b x y ha hb
    cases operation with
    | zero => exact expr.monotone a b x y ha hb
    | succ operation => exact ih operation a b x y ha hb

inductive FunctionsLe : List Expr → List Expr → Prop where
  | nil : FunctionsLe [] []
  | cons {a b left right} : ExprLe a b → FunctionsLe left right →
      FunctionsLe (a :: left) (b :: right)

theorem FunctionsLe.sound {smaller larger : List Expr}
    (proof : FunctionsLe smaller larger) : ChargesLe (charges smaller) (charges larger) := by
  induction proof with
  | nil =>
    intro _ _ _
    exact Nat.le_refl _
  | cons head _tail ih =>
    intro operation left right
    cases operation with
    | zero => exact head.sound left right
    | succ operation => exact ih operation left right

theorem budgetMonotone (budget : ReductionBounds.IntegerCost.Budget)
    {smaller larger : ReductionBounds.IntegerCost.Charges}
    (ordered : ChargesLe smaller larger) :
    budget.eval smaller ≤ budget.eval larger := by
  induction budget with
  | zero => exact Nat.le_refl _
  | item operation left right => exact ordered operation left right
  | add _left _right leftIH rightIH => exact Nat.add_le_add leftIH rightIH
  | max _left _right leftIH rightIH =>
    exact Nat.max_le.mpr
      ⟨Nat.le_trans leftIH (Nat.le_max_left _ _),
       Nat.le_trans rightIH (Nat.le_max_right _ _)⟩

end ReductionBounds.CostContract
