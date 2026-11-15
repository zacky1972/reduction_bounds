namespace ReductionBounds.Periodic

structure Run (State : Type) where
  state : State
  events : Nat
  cost : Nat

def run (next : State → Item → State) (event cost : State → Item → Nat)
    (state : State) : List Item → Run State
  | [] => ⟨state, 0, 0⟩
  | item :: rest =>
    let suffix := run next event cost (next state item) rest
    ⟨suffix.state, event state item + suffix.events, cost state item + suffix.cost⟩

structure Rule (State Item : Type) where
  period : Nat
  stride : Nat
  origin : Nat
  size : State → Nat
  invariant : State → Prop
  next : State → Item → State
  event : State → Item → Nat
  cost : State → Item → Nat
  base : Nat
  surcharge : Nat

def Rule.run (rule : Rule State Item) (state : State) (items : List Item) : Run State :=
  ReductionBounds.Periodic.run rule.next rule.event rule.cost state items

structure Obligations (rule : Rule State Item) : Prop where
  positive : 0 < rule.period
  range : ∀ state, rule.invariant state → rule.size state < rule.period + rule.origin
  preserves : ∀ state item, rule.invariant state → rule.invariant (rule.next state item)
  advance : ∀ state item, rule.invariant state →
    rule.size state + rule.stride = rule.event state item * rule.period +
        rule.size (rule.next state item) ∧
      rule.origin ≤ rule.size (rule.next state item)
  budget : ∀ state item, rule.invariant state →
    rule.cost state item ≤ rule.base + rule.event state item * rule.surcharge

def eventFormula (period stride origin initial steps : Nat) : Nat :=
  (initial + steps * stride - origin) / period

def costFormula (base surcharge events steps : Nat) : Nat :=
  steps * base + events * surcharge

theorem accumulate {rule : Rule State Item} (checked : Obligations rule)
    (state : State) (items : List Item) (valid : rule.invariant state) :
    let result := rule.run state items
    rule.invariant result.state ∧
      rule.size state + items.length * rule.stride =
        result.events * rule.period + rule.size result.state ∧
      (items ≠ [] → rule.origin ≤ rule.size result.state) ∧
      result.cost ≤ costFormula rule.base rule.surcharge result.events items.length := by
  induction items generalizing state with
  | nil => simp [Rule.run, run, costFormula, valid]
  | cons item rest ih =>
    have nextValid := checked.preserves state item valid
    obtain ⟨endValid, balance, lands, budget⟩ := ih (rule.next state item) nextValid
    obtain ⟨advance, nextLands⟩ := checked.advance state item valid
    have stepBudget := checked.budget state item valid
    have endLands : rule.origin ≤ rule.size (rule.run (rule.next state item) rest).state := by
      cases rest with
      | nil => exact nextLands
      | cons head tail => exact lands (by simp)
    simp only [Rule.run, run, List.length_cons, Nat.add_mul, Nat.one_mul, costFormula] at *
    refine ⟨endValid, by omega, fun _ => endLands, ?_⟩
    omega

theorem eventCount {rule : Rule State Item} (checked : Obligations rule)
    (state : State) (items : List Item) (valid : rule.invariant state) :
    (rule.run state items).events =
      eventFormula rule.period rule.stride rule.origin (rule.size state) items.length := by
  cases items with
  | nil =>
    have positive := checked.positive
    have inRange := checked.range state valid
    simp only [Rule.run, run, eventFormula, List.length_nil, Nat.zero_mul, Nat.add_zero]
    exact (Nat.div_eq_of_lt (by omega)).symm
  | cons item rest =>
    obtain ⟨endValid, balance, lands, _⟩ := accumulate checked state (item :: rest) valid
    have below := checked.range _ endValid
    have above := lands (by simp)
    unfold eventFormula
    symm
    apply Nat.div_eq_of_lt_le
    · omega
    · rw [Nat.add_mul, Nat.one_mul]
      omega

theorem costBound {rule : Rule State Item} (checked : Obligations rule)
    (state : State) (items : List Item) (valid : rule.invariant state) :
    (rule.run state items).cost ≤ costFormula rule.base rule.surcharge
      (eventFormula rule.period rule.stride rule.origin (rule.size state) items.length) items.length := by
  rw [← eventCount checked state items valid]
  exact (accumulate checked state items valid).2.2.2

theorem annotated {rule : Rule State Item} (checked : Obligations rule)
    (invariant : State → Prop) (measure : State → Nat)
    (preserves : ∀ state item, rule.invariant state → invariant state →
      invariant (rule.next state item))
    (covers : ∀ state, rule.invariant state → invariant state → rule.size state ≤ measure state)
    (state : State) (items : List Item) (valid : rule.invariant state) (initial : invariant state) :
    let result := rule.run state items
    let cap := eventFormula rule.period rule.stride rule.origin (measure state) items.length
    invariant result.state ∧ result.events ≤ cap ∧
      result.cost ≤ costFormula rule.base rule.surcharge cap items.length := by
  have keeps : invariant (rule.run state items).state := by
    induction items generalizing state with
    | nil => exact initial
    | cons item rest ih =>
      exact ih (rule.next state item) (checked.preserves state item valid) (preserves state item valid initial)
  have sourceBound := covers state valid initial
  have eventLe : (rule.run state items).events ≤
      eventFormula rule.period rule.stride rule.origin (measure state) items.length := by
    rw [eventCount checked state items valid]
    unfold eventFormula
    exact Nat.div_le_div_right (by omega)
  exact ⟨keeps, eventLe, Nat.le_trans (accumulate checked state items valid).2.2.2
    (Nat.add_le_add_left (Nat.mul_le_mul_right rule.surcharge eventLe) _)⟩

-- A counter accepts a fixed number of items per step and emits a group
-- whenever the advancing count reaches the threshold.
def counterStep (period stride state : Nat) : Nat × Bool :=
  let advanced := state + stride
  if period ≤ advanced then (advanced - period, true) else (advanced, false)

def counterRule (period stride base surcharge : Nat) : Rule Nat Unit := {
  period, stride, origin := 0
  size := id
  invariant := fun state => state < period
  next := fun state _ => (counterStep period stride state).1
  event := fun state _ => (counterStep period stride state).2.toNat
  cost := fun state _ => base + (counterStep period stride state).2.toNat * surcharge
  base, surcharge
}

theorem counterObligations (period stride base surcharge : Nat)
    (stridePositive : 0 < stride) (fits : stride ≤ period) :
    Obligations (counterRule period stride base surcharge) := by
  refine ⟨by change 0 < period; omega, ?_, ?_, ?_, ?_⟩
  · intro state valid
    simpa [counterRule] using valid
  · intro state item valid
    change state < period at valid
    change (counterStep period stride state).1 < period
    by_cases reset : period ≤ state + stride
    · simp [counterStep, reset] <;> omega
    · simp [counterStep, reset] <;> omega
  · intro state item valid
    change state + stride = (counterStep period stride state).2.toNat * period +
      (counterStep period stride state).1 ∧ 0 ≤ (counterStep period stride state).1
    by_cases reset : period ≤ state + stride
    · simp [counterStep, reset] <;> omega
    · simp [counterStep, reset]
  · intro state item valid
    exact Nat.le_refl _

end ReductionBounds.Periodic
