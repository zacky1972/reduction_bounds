inductive CostExpr where
  | paid : Nat → CostExpr
  | seq : CostExpr → CostExpr → CostExpr
  | tail : CostExpr

def CostExpr.eval (tailCost : Nat) : CostExpr → Nat
  | .paid cost => cost
  | .seq left right => left.eval tailCost + right.eval tailCost
  | .tail => tailCost

def CostExpr.calls : CostExpr → Nat
  | .paid _ => 0
  | .seq left right => left.calls + right.calls
  | .tail => 1

theorem costComposition (expr : CostExpr) (tailCost : Nat) :
    expr.eval tailCost = expr.eval 0 + expr.calls * tailCost := by
  induction expr with
  | paid cost => simp [CostExpr.eval, CostExpr.calls]
  | seq left right leftIH rightIH =>
    simp only [CostExpr.eval, CostExpr.calls, Nat.add_mul, leftIH, rightIH]
    omega
  | tail => simp [CostExpr.eval, CostExpr.calls]

inductive ListCost (empty : CostExpr) (stops steps : List CostExpr) : Nat → Nat → Prop where
  | nil : ListCost empty stops steps 0 (empty.eval 0)
  | stop {size branch} : branch ∈ stops →
      ListCost empty stops steps (size + 1) (branch.eval 0)
  | step {size branch tailCost} : branch ∈ steps →
      ListCost empty stops steps size tailCost →
      ListCost empty stops steps (size + 1) (branch.eval tailCost)

theorem listRulesSound {empty stops steps size cost n base step}
    (derivation : ListCost empty stops steps size cost) (sizeBound : size ≤ n)
    (emptyBound : empty.eval 0 ≤ base)
    (stopBound : ∀ branch ∈ stops, branch.eval 0 ≤ base)
    (stepBound : ∀ branch ∈ steps, branch.eval 0 ≤ step ∧ branch.calls ≤ 1) :
    cost ≤ base + n * step := by
  have exactBound : cost ≤ base + size * step := by
    induction derivation with
    | nil => simpa using emptyBound
    | stop member =>
      exact Nat.le_trans (stopBound _ member) (Nat.le_add_right _ _)
    | @step size branch tailCost member _ ih =>
      obtain ⟨localBound, countBound⟩ := stepBound branch member
      have recursiveBound := Nat.mul_le_mul_right tailCost countBound
      rw [Nat.one_mul] at recursiveBound
      have tailBound := ih (by omega : size ≤ n)
      rw [costComposition, Nat.succ_mul]
      omega
  exact Nat.le_trans exactBound
    (Nat.add_le_add_left (Nat.mul_le_mul_right step sizeBound) _)

theorem listPathBounds {empty stops steps size cost stop step}
    (derivation : ListCost empty stops steps size cost)
    (stopBound : ∀ branch ∈ stops, branch.eval 0 ≤ stop)
    (stepBound : ∀ branch ∈ steps, branch.eval 0 ≤ step ∧ branch.calls ≤ 1) :
    cost ≤ empty.eval 0 + size * step ∨
      (stops ≠ [] ∧ 0 < size ∧ cost ≤ stop + (size - 1) * step) := by
  induction derivation with
  | nil => exact Or.inl (by simp)
  | @stop size branch member =>
    right
    refine ⟨?_, by omega, ?_⟩
    · intro noStops
      simp [noStops] at member
    · exact Nat.le_trans (stopBound branch member) (Nat.le_add_right _ _)
  | @step size branch tailCost member _ ih =>
    obtain ⟨localBound, countBound⟩ := stepBound branch member
    have recursiveBound := Nat.mul_le_mul_right tailCost countBound
    rw [Nat.one_mul] at recursiveBound
    rw [costComposition]
    rcases ih with emptyPath | ⟨hasStop, positive, stopPath⟩
    · left
      rw [Nat.succ_mul]
      omega
    · right
      refine ⟨hasStop, by omega, ?_⟩
      have sizeEq : size = (size - 1) + 1 := by omega
      have sizeCost : size * step = (size - 1) * step + step := by
        conv => lhs; rw [sizeEq]
        rw [Nat.succ_mul]
      simp only [Nat.add_sub_cancel]
      omega

