def searchCost (empty hit step : Nat) (key : Int) : List Int → Nat
  | [] => empty
  | head :: tail => if head = key then hit else step + searchCost empty hit step key tail

theorem searchCostBound (empty hit step : Nat) (key : Int) (xs : List Int) (n : Nat)
    (sizeBound : xs.length ≤ n) :
    searchCost empty hit step key xs ≤ max empty hit + n * step := by
  have exactLength (ys : List Int) :
      searchCost empty hit step key ys ≤ max empty hit + ys.length * step := by
    induction ys with
    | nil =>
        simpa [searchCost] using (Nat.le_max_left empty hit)
    | cons head tail ih =>
        by_cases equal : head = key
        · simp only [searchCost, if_pos equal]
          exact Nat.le_trans (Nat.le_max_right empty hit) (Nat.le_add_right _ _)
        · simp only [searchCost, if_neg equal, List.length_cons, Nat.succ_mul]
          omega
  exact Nat.le_trans (exactLength xs)
    (Nat.add_le_add_left (Nat.mul_le_mul_right step sizeBound) _)
