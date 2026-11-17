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

/-- A candidate nearest zero; it satisfies every constraint whenever any value does. -/
def Bounds.witness (bounds : Bounds) : Int :=
  match bounds.lower, bounds.upper with
  | some lower, some upper => max lower (min 0 upper)
  | some lower, none => max lower 0
  | none, some upper => min 0 upper
  | none, none => 0

theorem witnessHolds (bounds : Bounds) (value : Int) (held : Holds bounds value) :
    Holds bounds bounds.witness := by
  rcases bounds with ⟨lower, upper, bits⟩
  cases lower <;> cases upper <;> cases bits <;>
    simp [Holds, LowerHolds, UpperHolds, MagnitudeHolds, Bounds.witness] at * <;> omega

/-- Separate unconstrained integer information from the empty set. -/
inductive Domain where
  | bounded (bounds : Bounds)
  | unreachable
  deriving DecidableEq

def Domain.Holds : Domain → Int → Prop
  | .bounded bounds, value => ReductionBounds.IntegerSize.Holds bounds value
  | .unreachable, _ => False

instance (domain : Domain) (value : Int) : Decidable (domain.Holds value) := by
  cases domain <;> unfold Domain.Holds <;> infer_instance

def Domain.contains (domain : Domain) (value : Int) : Bool :=
  decide (domain.Holds value)

/-- Preserve satisfiable constraints and replace empty constraints by unreachable. -/
def Domain.normalize : Domain → Domain
  | .unreachable => .unreachable
  | .bounded bounds =>
    if ReductionBounds.IntegerSize.contains bounds bounds.witness then
      .bounded bounds
    else
      .unreachable

theorem domainContainsCorrect (domain : Domain) (value : Int) :
    domain.contains value = true ↔ domain.Holds value := by
  simp [Domain.contains]

theorem unknownHolds (value : Int) : Domain.Holds (.bounded {}) value :=
  unconstrained value

theorem unreachableHolds (value : Int) : ¬ Domain.Holds .unreachable value := by
  simp [Domain.Holds]

theorem normalizeSound (domain : Domain) (value : Int) :
    domain.normalize.Holds value ↔ domain.Holds value := by
  cases domain with
  | unreachable => rfl
  | bounded bounds =>
    by_cases witness : Holds bounds bounds.witness
    · simp [Domain.normalize, contains, witness, Domain.Holds]
    · have empty : ¬ Holds bounds value := fun held => witness (witnessHolds bounds value held)
      simp [Domain.normalize, contains, witness, Domain.Holds, empty]

theorem normalizeUnreachableIff (domain : Domain) :
    domain.normalize = .unreachable ↔ ¬ ∃ value, domain.Holds value := by
  cases domain with
  | unreachable => simp [Domain.normalize, Domain.Holds]
  | bounded bounds =>
    by_cases witness : Holds bounds bounds.witness
    · have existsValue : ∃ value, Holds bounds value := ⟨bounds.witness, witness⟩
      simp [Domain.normalize, contains, witness, Domain.Holds, existsValue]
    · have empty : ¬ ∃ value, Holds bounds value := by
        rintro ⟨value, held⟩
        exact witness (witnessHolds bounds value held)
      simp [Domain.normalize, contains, witness, Domain.Holds, empty]

theorem normalizeIdempotent (domain : Domain) :
    domain.normalize.normalize = domain.normalize := by
  cases domain with
  | unreachable => rfl
  | bounded bounds =>
    by_cases witness : contains bounds bounds.witness = true <;>
      simp [Domain.normalize, witness]

theorem unknownNotUnreachable : Domain.normalize (.bounded {}) ≠ .unreachable := by
  simp [Domain.normalize, contains, Holds, LowerHolds, UpperHolds, MagnitudeHolds]

end ReductionBounds.IntegerSize
