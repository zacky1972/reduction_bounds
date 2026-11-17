namespace ReductionBounds.IntegerSize

/-- A missing component imposes no constraint on the integer. -/
structure Bounds where
  lower : Option Int := none
  upper : Option Int := none
  magnitudeBits : Option Nat := none
  deriving DecidableEq

def LowerHolds (lower : Option Int) (value : Int) : Prop :=
  match lower with
  | none => True
  | some endpoint => endpoint ≤ value

def UpperHolds (upper : Option Int) (value : Int) : Prop :=
  match upper with
  | none => True
  | some endpoint => value ≤ endpoint

def MagnitudeHolds (bits : Option Nat) (value : Int) : Prop :=
  match bits with
  | none => True
  | some width => value.natAbs < 2 ^ width

/-- Concretization: all three constraints hold for the same integer. -/
def Holds (bounds : Bounds) (value : Int) : Prop :=
  LowerHolds bounds.lower value ∧ UpperHolds bounds.upper value ∧
    MagnitudeHolds bounds.magnitudeBits value

instance (lower : Option Int) (value : Int) : Decidable (LowerHolds lower value) := by
  unfold LowerHolds
  split <;> infer_instance

instance (upper : Option Int) (value : Int) : Decidable (UpperHolds upper value) := by
  unfold UpperHolds
  split <;> infer_instance

instance (bits : Option Nat) (value : Int) : Decidable (MagnitudeHolds bits value) := by
  unfold MagnitudeHolds
  split <;> infer_instance

instance (bounds : Bounds) (value : Int) : Decidable (Holds bounds value) := by
  unfold Holds
  infer_instance

def contains (bounds : Bounds) (value : Int) : Bool :=
  decide (Holds bounds value)

theorem containsCorrect (bounds : Bounds) (value : Int) :
    contains bounds value = true ↔ Holds bounds value := by
  simp [contains]

theorem unconstrained (value : Int) :
    Holds {} value := by
  simp [Holds, LowerHolds, UpperHolds, MagnitudeHolds]

theorem lowerBound (bounds : Bounds) (value endpoint : Int)
    (held : Holds bounds value) (specified : bounds.lower = some endpoint) :
    endpoint ≤ value := by
  have lower := held.1
  simpa [LowerHolds, specified] using lower

theorem upperBound (bounds : Bounds) (value endpoint : Int)
    (held : Holds bounds value) (specified : bounds.upper = some endpoint) :
    value ≤ endpoint := by
  have upper := held.2.1
  simpa [UpperHolds, specified] using upper

theorem magnitudeBound (bounds : Bounds) (value : Int) (width : Nat)
    (held : Holds bounds value) (specified : bounds.magnitudeBits = some width) :
    value.natAbs < 2 ^ width := by
  have magnitude := held.2.2
  simpa [MagnitudeHolds, specified] using magnitude

theorem zeroMagnitude (value : Int) :
    Holds { magnitudeBits := some 0 } value ↔ value = 0 := by
  simp [Holds, LowerHolds, UpperHolds, MagnitudeHolds]

theorem reversedRange (lower upper : Int) (reversed : upper < lower) (value : Int) :
    ¬ Holds { lower := some lower, upper := some upper } value := by
  simp only [Holds, LowerHolds, UpperHolds, MagnitudeHolds]
  omega

end ReductionBounds.IntegerSize
