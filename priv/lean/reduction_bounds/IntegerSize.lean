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


def magnitudeBits (value : Int) : Nat :=
  if value = 0 then 0 else value.natAbs.log2 + 1

theorem magnitudeBitsCorrect (value : Int) : value.natAbs < 2 ^ magnitudeBits value := by
  by_cases zero : value = 0
  · simp [magnitudeBits, zero]
  · have nonzero : value.natAbs ≠ 0 := by omega
    simpa [magnitudeBits, zero] using
      (Nat.log2_lt nonzero).mp (by omega : value.natAbs.log2 < value.natAbs.log2 + 1)

theorem magnitudeBitsMinimal (value : Int) (width : Nat)
    (bound : value.natAbs < 2 ^ width) : magnitudeBits value ≤ width := by
  by_cases zero : value = 0
  · simp [magnitudeBits, zero]
  · have nonzero : value.natAbs ≠ 0 := by omega
    have := (Nat.log2_lt nonzero).mpr bound
    simp [magnitudeBits, zero]
    omega

def singleton (value : Int) : Bounds :=
  ⟨some value, some value, some (magnitudeBits value)⟩

theorem singletonExact (constant value : Int) : Holds (singleton constant) value ↔ value = constant := by
  constructor
  · intro held
    simp only [Holds, singleton, LowerHolds, UpperHolds] at held
    omega
  · rintro rfl
    exact ⟨Int.le_refl _, Int.le_refl _, magnitudeBitsCorrect value⟩

def endpointAdd : Option Int → Option Int → Option Int
  | some left, some right => some (left + right)
  | _, _ => none

def endpointSubtract : Option Int → Option Int → Option Int
  | some left, some right => some (left - right)
  | _, _ => none

def addBits : Option Nat → Option Nat → Option Nat
  | some left, some right => some (max left right + 1)
  | _, _ => none

def multiplyBits : Option Nat → Option Nat → Option Nat
  | some left, some right => some (left + right)
  | _, _ => none

theorem lowerAddSound (left right : Option Int) (u v : Int)
    (hu : LowerHolds left u) (hv : LowerHolds right v) :
    LowerHolds (endpointAdd left right) (u + v) := by
  cases left <;> cases right <;> simp_all [LowerHolds, endpointAdd] <;> omega

theorem upperAddSound (left right : Option Int) (u v : Int)
    (hu : UpperHolds left u) (hv : UpperHolds right v) :
    UpperHolds (endpointAdd left right) (u + v) := by
  cases left <;> cases right <;> simp_all [UpperHolds, endpointAdd] <;> omega

theorem lowerSubtractSound (left right : Option Int) (u v : Int)
    (hu : LowerHolds left u) (hv : UpperHolds right v) :
    LowerHolds (endpointSubtract left right) (u - v) := by
  cases left <;> cases right <;> simp_all [LowerHolds, UpperHolds, endpointSubtract] <;> omega

theorem upperSubtractSound (left right : Option Int) (u v : Int)
    (hu : UpperHolds left u) (hv : LowerHolds right v) :
    UpperHolds (endpointSubtract left right) (u - v) := by
  cases left <;> cases right <;> simp_all [LowerHolds, UpperHolds, endpointSubtract] <;> omega

theorem addMagnitudeBound (u v : Int) (a b : Nat)
    (hu : u.natAbs < 2 ^ a) (hv : v.natAbs < 2 ^ b) :
    (u + v).natAbs < 2 ^ (max a b + 1) ∧ (u - v).natAbs < 2 ^ (max a b + 1) := by
  have leftCap := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_max_left a b)
  have rightCap := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_max_right a b)
  have sumBound : (u + v).natAbs ≤ u.natAbs + v.natAbs := by omega
  have differenceBound : (u - v).natAbs ≤ u.natAbs + v.natAbs := by omega
  rw [Nat.pow_succ]
  omega

theorem addBitsSound (left right : Option Nat) (u v : Int)
    (hu : MagnitudeHolds left u) (hv : MagnitudeHolds right v) :
    MagnitudeHolds (addBits left right) (u + v) ∧
    MagnitudeHolds (addBits left right) (u - v) := by
  cases left with
  | none => simp [addBits, MagnitudeHolds]
  | some a =>
    cases right with
    | none => simp [addBits, MagnitudeHolds]
    | some b => exact addMagnitudeBound u v a b hu hv

theorem multiplyMagnitudeBound (u v : Int) (a b : Nat)
    (hu : u.natAbs < 2 ^ a) (hv : v.natAbs < 2 ^ b) :
    (u * v).natAbs < 2 ^ (a + b) := by
  rw [Int.natAbs_mul, Nat.pow_add]
  by_cases zero : v.natAbs = 0
  · simp [zero, Nat.pow_pos (a := 2) (by decide)]
  · have product := Nat.mul_lt_mul_of_pos_right hu (by omega : 0 < v.natAbs)
    exact Nat.lt_of_lt_of_le product (Nat.mul_le_mul_left _ (Nat.le_of_lt hv))

theorem multiplyBitsSound (left right : Option Nat) (u v : Int)
    (hu : MagnitudeHolds left u) (hv : MagnitudeHolds right v) :
    MagnitudeHolds (multiplyBits left right) (u * v) := by
  cases left with
  | none => simp [multiplyBits, MagnitudeHolds]
  | some a =>
    cases right with
    | none => simp [multiplyBits, MagnitudeHolds]
    | some b => exact multiplyMagnitudeBound u v a b hu hv

def Bounds.add (left right : Bounds) : Bounds :=
  ⟨endpointAdd left.lower right.lower, endpointAdd left.upper right.upper,
    addBits left.magnitudeBits right.magnitudeBits⟩

def Bounds.subtract (left right : Bounds) : Bounds :=
  ⟨endpointSubtract left.lower right.upper, endpointSubtract left.upper right.lower,
    addBits left.magnitudeBits right.magnitudeBits⟩

theorem boundsAddSound (left right : Bounds) (u v : Int)
    (hu : Holds left u) (hv : Holds right v) : Holds (left.add right) (u + v) :=
  ⟨lowerAddSound _ _ u v hu.1 hv.1, upperAddSound _ _ u v hu.2.1 hv.2.1,
    (addBitsSound _ _ u v hu.2.2 hv.2.2).1⟩

theorem boundsSubtractSound (left right : Bounds) (u v : Int)
    (hu : Holds left u) (hv : Holds right v) : Holds (left.subtract right) (u - v) :=
  ⟨lowerSubtractSound _ _ u v hu.1 hv.2.1, upperSubtractSound _ _ u v hu.2.1 hv.1,
    (addBitsSound _ _ u v hu.2.2 hv.2.2).2⟩

theorem scaledInterval (lower value upper factor : Int)
    (lo : lower ≤ value) (hi : value ≤ upper) :
    min (lower * factor) (upper * factor) ≤ value * factor ∧
    value * factor ≤ max (lower * factor) (upper * factor) := by
  by_cases nonnegative : 0 ≤ factor
  · have left := Int.mul_le_mul_of_nonneg_right lo nonnegative
    have right := Int.mul_le_mul_of_nonneg_right hi nonnegative
    omega
  · have left := Int.mul_le_mul_of_nonpos_right lo (by omega : factor ≤ 0)
    have right := Int.mul_le_mul_of_nonpos_right hi (by omega : factor ≤ 0)
    omega

theorem productInterval (a b c d u v : Int)
    (hu : a ≤ u ∧ u ≤ b) (hv : c ≤ v ∧ v ≤ d) :
    min (min (a * c) (a * d)) (min (b * c) (b * d)) ≤ u * v ∧
    u * v ≤ max (max (a * c) (a * d)) (max (b * c) (b * d)) := by
  have valueBounds := scaledInterval a u b v hu.1 hu.2
  have leftBounds := scaledInterval c v d a hv.1 hv.2
  have rightBounds := scaledInterval c v d b hv.1 hv.2
  simp only [Int.mul_comm] at leftBounds rightBounds
  omega

def productRange : Option Int → Option Int → Option Int → Option Int → Option Int × Option Int
  | some a, some b, some c, some d =>
    (some (min (min (a * c) (a * d)) (min (b * c) (b * d))),
     some (max (max (a * c) (a * d)) (max (b * c) (b * d))))
  | _, _, _, _ => (none, none)

theorem productRangeSound (a b c d : Option Int) (u v : Int)
    (hu : LowerHolds a u ∧ UpperHolds b u) (hv : LowerHolds c v ∧ UpperHolds d v) :
    LowerHolds (productRange a b c d).1 (u * v) ∧
    UpperHolds (productRange a b c d).2 (u * v) := by
  cases a <;> cases b <;> cases c <;> cases d <;>
    simp_all only [productRange, LowerHolds, UpperHolds, true_and, and_true]
  exact productInterval _ _ _ _ u v hu hv

def Bounds.isZero (bounds : Bounds) : Bool :=
  decide (bounds.magnitudeBits = some 0 ∨ bounds.lower = some 0 ∧ bounds.upper = some 0)

theorem zeroValue (bounds : Bounds) (value : Int)
    (zero : bounds.isZero = true) (held : Holds bounds value) : value = 0 := by
  have test := of_decide_eq_true zero
  rcases test with bits | ⟨lo, hi⟩
  · have bound := magnitudeBound bounds value 0 held bits
    simp only [Nat.pow_zero] at bound
    omega
  · have lower := lowerBound bounds value 0 held lo
    have upper := upperBound bounds value 0 held hi
    omega

def Bounds.multiply (left right : Bounds) : Bounds :=
  if left.isZero || right.isZero then singleton 0 else
    let range := productRange left.lower left.upper right.lower right.upper
    ⟨range.1, range.2, multiplyBits left.magnitudeBits right.magnitudeBits⟩

theorem boundsMultiplySound (left right : Bounds) (u v : Int)
    (hu : Holds left u) (hv : Holds right v) : Holds (left.multiply right) (u * v) := by
  unfold Bounds.multiply
  split
  · rename_i zero
    simp only [Bool.or_eq_true] at zero
    rcases zero with zero | zero
    · apply (singletonExact _ _).mpr
      rw [zeroValue left u zero hu, Int.zero_mul]
    · apply (singletonExact _ _).mpr
      rw [zeroValue right v zero hv, Int.mul_zero]
  · have range := productRangeSound left.lower left.upper right.lower right.upper u v
      ⟨hu.1, hu.2.1⟩ ⟨hv.1, hv.2.1⟩
    exact ⟨range.1, range.2, multiplyBitsSound _ _ u v hu.2.2 hv.2.2⟩

def Domain.binary (operation : Bounds → Bounds → Bounds) (left right : Domain) : Domain :=
  match left.normalize, right.normalize with
  | .bounded a, .bounded b => (Domain.bounded (operation a b)).normalize
  | _, _ => .unreachable

theorem binarySound (operation : Bounds → Bounds → Bounds) (evaluate : Int → Int → Int)
    (sound : ∀ a b u v, Holds a u → Holds b v → Holds (operation a b) (evaluate u v))
    (left right : Domain) (u v : Int) (hu : left.Holds u) (hv : right.Holds v) :
    (Domain.binary operation left right).Holds (evaluate u v) := by
  have leftHeld := (normalizeSound left u).mpr hu
  have rightHeld := (normalizeSound right v).mpr hv
  unfold Domain.binary
  cases leftCase : left.normalize with
  | unreachable => simp [leftCase, Domain.Holds] at leftHeld
  | bounded a =>
    cases rightCase : right.normalize with
    | unreachable => simp [rightCase, Domain.Holds] at rightHeld
    | bounded b =>
      simp only [leftCase, rightCase, Domain.Holds] at leftHeld rightHeld ⊢
      exact (normalizeSound (Domain.bounded (operation a b)) (evaluate u v)).mpr
        (sound a b u v leftHeld rightHeld)

def Domain.add : Domain → Domain → Domain := Domain.binary Bounds.add

def Domain.subtract : Domain → Domain → Domain := Domain.binary Bounds.subtract

def Domain.multiply : Domain → Domain → Domain := Domain.binary Bounds.multiply

theorem addSound (left right : Domain) (u v : Int) (hu : left.Holds u) (hv : right.Holds v) :
    (left.add right).Holds (u + v) :=
  binarySound Bounds.add (· + ·) boundsAddSound left right u v hu hv

theorem subtractSound (left right : Domain) (u v : Int) (hu : left.Holds u) (hv : right.Holds v) :
    (left.subtract right).Holds (u - v) :=
  binarySound Bounds.subtract (· - ·) boundsSubtractSound left right u v hu hv

theorem multiplySound (left right : Domain) (u v : Int) (hu : left.Holds u) (hv : right.Holds v) :
    (left.multiply right).Holds (u * v) :=
  binarySound Bounds.multiply (· * ·) boundsMultiplySound left right u v hu hv


/-- Mathematical left shift, for any signed integer and a natural amount. -/
def shiftValue (value : Int) (amount : Nat) : Int := value <<< amount

theorem shiftValueMultiply (value : Int) (amount : Nat) :
    shiftValue value amount = value * 2 ^ amount := Int.shiftLeft_eq value amount

def scaleEndpoint (endpoint : Option Int) (amount : Nat) : Option Int :=
  endpoint.map (fun value => value * 2 ^ amount)

def shiftBits (bits : Option Nat) (amount : Nat) : Option Nat :=
  bits.map (· + amount)

theorem lowerShiftSound (endpoint : Option Int) (value : Int) (amount : Nat)
    (held : LowerHolds endpoint value) :
    LowerHolds (scaleEndpoint endpoint amount) (shiftValue value amount) := by
  cases endpoint with
  | none => trivial
  | some lower =>
    change lower * (2 : Int) ^ amount ≤ shiftValue value amount
    rw [shiftValueMultiply]
    exact Int.mul_le_mul_of_nonneg_right held
      (Int.le_of_lt (Int.pow_pos (n := 2) (m := amount) (by decide)))

theorem upperShiftSound (endpoint : Option Int) (value : Int) (amount : Nat)
    (held : UpperHolds endpoint value) :
    UpperHolds (scaleEndpoint endpoint amount) (shiftValue value amount) := by
  cases endpoint with
  | none => trivial
  | some upper =>
    change shiftValue value amount ≤ upper * (2 : Int) ^ amount
    rw [shiftValueMultiply]
    exact Int.mul_le_mul_of_nonneg_right held
      (Int.le_of_lt (Int.pow_pos (n := 2) (m := amount) (by decide)))

theorem shiftMagnitudeBound (value : Int) (width amount : Nat)
    (held : value.natAbs < 2 ^ width) :
    (shiftValue value amount).natAbs < 2 ^ (width + amount) := by
  rw [shiftValueMultiply, Int.natAbs_mul, Int.natAbs_pow, Nat.pow_add]
  exact Nat.mul_lt_mul_of_pos_right held (Nat.pow_pos (by decide))

theorem shiftBitsSound (bits : Option Nat) (value : Int) (amount : Nat)
    (held : MagnitudeHolds bits value) :
    MagnitudeHolds (shiftBits bits amount) (shiftValue value amount) := by
  cases bits with
  | none => trivial
  | some width => exact shiftMagnitudeBound value width amount held

def Bounds.shiftLeft (bounds : Bounds) (amount : Nat) : Bounds :=
  if bounds.isZero then singleton 0 else
    ⟨scaleEndpoint bounds.lower amount, scaleEndpoint bounds.upper amount,
      shiftBits bounds.magnitudeBits amount⟩

theorem boundsShiftLeftSound (bounds : Bounds) (value : Int) (amount : Nat)
    (held : Holds bounds value) : Holds (bounds.shiftLeft amount) (shiftValue value amount) := by
  unfold Bounds.shiftLeft
  split
  · rename_i zero
    apply (singletonExact _ _).mpr
    rw [shiftValueMultiply, zeroValue bounds value zero held, Int.zero_mul]
  · exact ⟨lowerShiftSound _ _ _ held.1, upperShiftSound _ _ _ held.2.1,
      shiftBitsSound _ _ _ held.2.2⟩

/-- Low bits are characterized by the unique nonnegative residue modulo 2^width. -/
def maskValue (value : Int) (width : Nat) : Int := value % 2 ^ width

theorem maskRange (value : Int) (width : Nat) :
    0 ≤ maskValue value width ∧ maskValue value width < 2 ^ width := by
  have positive : (0 : Int) < 2 ^ width := Int.pow_pos (by decide)
  exact ⟨Int.emod_nonneg value (by omega), Int.emod_lt_of_pos value positive⟩

theorem maskResidue (value : Int) (width : Nat) :
    maskValue value width % 2 ^ width = value % 2 ^ width :=
  Int.emod_emod value (2 ^ width)

theorem maskUnique (value result : Int) (width : Nat)
    (range : 0 ≤ result ∧ result < 2 ^ width)
    (residue : result % 2 ^ width = value % 2 ^ width) : result = maskValue value width := by
  rw [Int.emod_eq_of_lt range.1 range.2] at residue
  exact residue

theorem maskMagnitudeBound (value : Int) (width : Nat) :
    (maskValue value width).natAbs < 2 ^ width := by
  obtain ⟨nonnegative, upper⟩ := maskRange value width
  have absolute := Int.natAbs_of_nonneg nonnegative
  have power : (2 : Int) ^ width = ((2 ^ width : Nat) : Int) := (Int.natCast_pow 2 width).symm
  rw [power] at upper
  omega

theorem maskZeroWidth (value : Int) : maskValue value 0 = 0 := by
  simp [maskValue]

theorem maskInRange (value : Int) (width : Nat)
    (range : 0 ≤ value ∧ value < 2 ^ width) : maskValue value width = value :=
  Int.emod_eq_of_lt range.1 range.2

theorem maskNegativeOne (width : Nat) : maskValue (-1) width = 2 ^ width - 1 := by
  have positive : (0 : Int) < 2 ^ width := Int.pow_pos (by decide)
  apply (maskUnique (-1) (2 ^ width - 1) width (by omega) ?_).symm
  simp

theorem maskAfterFullShift (value : Int) (width : Nat) :
    maskValue (shiftValue value width) width = 0 := by
  simp [maskValue, shiftValueMultiply]

def Bounds.mask (bounds : Bounds) (width : Nat) : Bounds :=
  if bounds.isZero then singleton 0 else ⟨some 0, some (2 ^ width - 1), some width⟩

theorem boundsMaskSound (bounds : Bounds) (value : Int) (width : Nat)
    (held : Holds bounds value) : Holds (bounds.mask width) (maskValue value width) := by
  unfold Bounds.mask
  split
  · rename_i zero
    apply (singletonExact _ _).mpr
    simp [maskValue, zeroValue bounds value zero held]
  · have range := maskRange value width
    exact ⟨range.1, by dsimp [UpperHolds]; omega, maskMagnitudeBound value width⟩

def Domain.unary (operation : Bounds → Bounds) (input : Domain) : Domain :=
  match input.normalize with
  | .bounded bounds => (Domain.bounded (operation bounds)).normalize
  | .unreachable => .unreachable

theorem unarySound (operation : Bounds → Bounds) (evaluate : Int → Int)
    (sound : ∀ bounds value, Holds bounds value → Holds (operation bounds) (evaluate value))
    (input : Domain) (value : Int) (held : input.Holds value) :
    (Domain.unary operation input).Holds (evaluate value) := by
  have normalized := (normalizeSound input value).mpr held
  unfold Domain.unary
  cases inputCase : input.normalize with
  | unreachable => simp [inputCase, Domain.Holds] at normalized
  | bounded bounds =>
    simp only [inputCase, Domain.Holds] at normalized ⊢
    exact (normalizeSound (Domain.bounded (operation bounds)) (evaluate value)).mpr
      (sound bounds value normalized)

def Domain.shiftLeft (input : Domain) (amount : Nat) : Domain :=
  Domain.unary (fun bounds => bounds.shiftLeft amount) input

def Domain.mask (input : Domain) (width : Nat) : Domain :=
  Domain.unary (fun bounds => bounds.mask width) input

theorem shiftLeftSound (input : Domain) (value : Int) (amount : Nat) (held : input.Holds value) :
    (input.shiftLeft amount).Holds (shiftValue value amount) :=
  unarySound (fun bounds => bounds.shiftLeft amount) (fun value => shiftValue value amount)
    (fun bounds value => boundsShiftLeftSound bounds value amount) input value held

theorem maskSound (input : Domain) (value : Int) (width : Nat) (held : input.Holds value) :
    (input.mask width).Holds (maskValue value width) :=
  unarySound (fun bounds => bounds.mask width) (fun value => maskValue value width)
    (fun bounds value => boundsMaskSound bounds value width) input value held


def rightValue (value : Int) (amount : Nat) : Int := value >>> amount

theorem rightMagnitude (value : Int) (amount : Nat) : (rightValue value amount).natAbs ≤ value.natAbs := by
  cases value with
  | ofNat n => exact Nat.shiftRight_le n amount
  | negSucc n =>
    change (n >>> amount) + 1 ≤ n + 1
    have := Nat.shiftRight_le n amount
    omega

theorem divideMonotone (a b divisor : Int) (positive : 0 < divisor) (ordered : a ≤ b) :
    a / divisor ≤ b / divisor := by
  apply (Int.le_ediv_iff_mul_le positive).mpr
  have := (Int.le_ediv_iff_mul_le positive).mp (Int.le_refl (a / divisor))
  omega

def divideEndpoint (endpoint : Option Int) (amount : Nat) : Option Int :=
  endpoint.map (fun value => value / (2 ^ amount : Nat))

def Bounds.shiftRight (bounds : Bounds) (amount : Nat) : Bounds :=
  ⟨divideEndpoint bounds.lower amount, divideEndpoint bounds.upper amount, bounds.magnitudeBits⟩

theorem boundsShiftRightSound (bounds : Bounds) (value : Int) (amount : Nat)
    (held : Holds bounds value) : Holds (bounds.shiftRight amount) (rightValue value amount) := by
  have positive : (0 : Int) < (2 ^ amount : Nat) := by exact_mod_cast Nat.pow_pos (a := 2) (by decide)
  refine ⟨?_, ?_, ?_⟩
  · cases lower : bounds.lower with
    | none => simp [Bounds.shiftRight, divideEndpoint, LowerHolds, lower]
    | some endpoint =>
      have lo := lowerBound bounds value endpoint held lower
      simpa [Bounds.shiftRight, divideEndpoint, LowerHolds, lower, rightValue, Int.shiftRight_eq_div_pow]
        using divideMonotone endpoint value _ positive lo
  · cases upper : bounds.upper with
    | none => simp [Bounds.shiftRight, divideEndpoint, UpperHolds, upper]
    | some endpoint =>
      have hi := upperBound bounds value endpoint held upper
      simpa [Bounds.shiftRight, divideEndpoint, UpperHolds, upper, rightValue, Int.shiftRight_eq_div_pow]
        using divideMonotone value endpoint _ positive hi
  · cases bits : bounds.magnitudeBits with
    | none => simp [Bounds.shiftRight, MagnitudeHolds, bits]
    | some width =>
      simpa [Bounds.shiftRight, MagnitudeHolds, bits] using
        Nat.lt_of_le_of_lt (rightMagnitude value amount) (magnitudeBound _ _ _ held bits)

def xorValue : Int → Int → Int
  | .ofNat a, .ofNat b => .ofNat (a ^^^ b)
  | .negSucc a, .negSucc b => .ofNat (a ^^^ b)
  | .ofNat a, .negSucc b => .negSucc (a ^^^ b)
  | .negSucc a, .ofNat b => .negSucc (a ^^^ b)

theorem xorMagnitude (u v : Int) (a b : Nat)
    (hu : u.natAbs < 2 ^ a) (hv : v.natAbs < 2 ^ b) :
    (xorValue u v).natAbs < 2 ^ (max a b + 1) := by
  have leftCap := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_max_left a b)
  have rightCap := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_max_right a b)
  have positive : 0 < 2 ^ max a b := Nat.pow_pos (by decide)
  cases u <;> cases v <;> rename_i x y
  all_goals
    simp only [Int.natAbs] at hu hv
    have cap := Nat.xor_lt_two_pow (x := x) (y := y) (n := max a b) (by omega) (by omega)
    simp only [xorValue, Int.natAbs]
    rw [Nat.pow_succ]
    omega

def Bounds.bitXor (left right : Bounds) : Bounds := ⟨none, none, addBits left.magnitudeBits right.magnitudeBits⟩

theorem boundsXorSound (left right : Bounds) (u v : Int) (hu : Holds left u) (hv : Holds right v) :
    Holds (left.bitXor right) (xorValue u v) := by
  refine ⟨trivial, trivial, ?_⟩
  cases a : left.magnitudeBits <;> cases b : right.magnitudeBits <;>
    simp [Bounds.bitXor, addBits, MagnitudeHolds, a, b]
  exact xorMagnitude u v _ _ (magnitudeBound _ _ _ hu a) (magnitudeBound _ _ _ hv b)

def Domain.shiftRight (input : Domain) (amount : Nat) : Domain :=
  Domain.unary (fun bounds => bounds.shiftRight amount) input

def Domain.bitXor : Domain → Domain → Domain := Domain.binary Bounds.bitXor

theorem shiftRightSound (input : Domain) (value : Int) (amount : Nat) (held : input.Holds value) :
    (input.shiftRight amount).Holds (rightValue value amount) :=
  unarySound _ _ (fun bounds value => boundsShiftRightSound bounds value amount) _ _ held

theorem xorSound (left right : Domain) (u v : Int) (hu : left.Holds u) (hv : right.Holds v) :
    (left.bitXor right).Holds (xorValue u v) := binarySound _ _ boundsXorSound _ _ _ _ hu hv

def joinLower : Option Int → Option Int → Option Int
  | some a, some b => some (min a b)
  | _, _ => none

def joinUpper : Option Int → Option Int → Option Int
  | some a, some b => some (max a b)
  | _, _ => none

def joinBits : Option Nat → Option Nat → Option Nat
  | some a, some b => some (max a b)
  | _, _ => none

def Bounds.join (a b : Bounds) : Bounds :=
  ⟨joinLower a.lower b.lower, joinUpper a.upper b.upper, joinBits a.magnitudeBits b.magnitudeBits⟩

theorem boundsJoinLeft (a b : Bounds) (value : Int) (held : Holds a value) : Holds (a.join b) value := by
  refine ⟨?_, ?_, ?_⟩
  · have lo := held.1
    cases al : a.lower <;> cases bl : b.lower <;>
      simp_all [Bounds.join, joinLower, LowerHolds] <;> omega
  · have hi := held.2.1
    cases au : a.upper <;> cases bu : b.upper <;>
      simp_all [Bounds.join, joinUpper, UpperHolds] <;> omega
  · have bits := held.2.2
    cases aw : a.magnitudeBits with
    | none => simp [Bounds.join, joinBits, MagnitudeHolds, aw]
    | some width =>
      cases bw : b.magnitudeBits with
      | none => simp [Bounds.join, joinBits, MagnitudeHolds, bw]
      | some other =>
        have cap := Nat.pow_le_pow_right (n := 2) (by decide) (Nat.le_max_left width other)
        simpa [Bounds.join, joinBits, MagnitudeHolds, aw, bw] using
          Nat.lt_of_lt_of_le (magnitudeBound a value width held aw) cap

theorem boundsJoinComm (a b : Bounds) : a.join b = b.join a := by
  rcases a with ⟨al, au, aw⟩
  rcases b with ⟨bl, bu, bw⟩
  cases al <;> cases bl <;> cases au <;> cases bu <;> cases aw <;> cases bw <;>
    simp [Bounds.join, joinLower, joinUpper, joinBits, Int.min_comm, Int.max_comm, Nat.max_comm]

def Domain.join (left right : Domain) : Domain :=
  match left.normalize, right.normalize with
  | .unreachable, b => b
  | a, .unreachable => a
  | .bounded a, .bounded b => (Domain.bounded (a.join b)).normalize

theorem joinLeftSound (left right : Domain) (value : Int) (held : left.Holds value) :
    (left.join right).Holds value := by
  have lh := (normalizeSound left value).mpr held
  unfold Domain.join
  cases lc : left.normalize with
  | unreachable => simp [lc, Domain.Holds] at lh
  | bounded a =>
    cases rc : right.normalize with
    | unreachable => simpa [lc, rc] using lh
    | bounded b =>
      simp only [lc, Domain.Holds] at lh ⊢
      exact (normalizeSound (Domain.bounded (a.join b)) value).mpr (boundsJoinLeft a b value lh)

theorem joinComm (left right : Domain) : left.join right = right.join left := by
  unfold Domain.join
  cases left.normalize <;> cases right.normalize <;> simp [boundsJoinComm]

theorem joinRightSound (left right : Domain) (value : Int) (held : right.Holds value) :
    (left.join right).Holds value := by
  rw [joinComm]
  exact joinLeftSound right left value held

inductive Comparison where
  | lt | le | eq | ne | ge | gt
  deriving DecidableEq

def Comparison.test (op : Comparison) (value constant : Int) : Bool :=
  match op with
  | .lt => decide (value < constant)
  | .le => decide (value ≤ constant)
  | .eq => decide (value = constant)
  | .ne => decide (value ≠ constant)
  | .ge => decide (constant ≤ value)
  | .gt => decide (constant < value)

def Bounds.lowerAtLeast (bounds : Bounds) (constant : Int) : Bounds :=
  { bounds with lower := some (match bounds.lower with | none => constant | some old => max old constant) }

def Bounds.upperAtMost (bounds : Bounds) (constant : Int) : Bounds :=
  { bounds with upper := some (match bounds.upper with | none => constant | some old => min old constant) }

theorem lowerAtLeastSound (bounds : Bounds) (constant value : Int) (held : Holds bounds value)
    (lower : constant ≤ value) : Holds (bounds.lowerAtLeast constant) value := by
  rcases held with ⟨lo, hi, bits⟩
  refine ⟨?_, hi, bits⟩
  cases lowerCase : bounds.lower <;> simp_all [Bounds.lowerAtLeast, LowerHolds] <;> omega

theorem upperAtMostSound (bounds : Bounds) (constant value : Int) (held : Holds bounds value)
    (upper : value ≤ constant) : Holds (bounds.upperAtMost constant) value := by
  rcases held with ⟨lo, hi, bits⟩
  refine ⟨lo, ?_, bits⟩
  cases upperCase : bounds.upper <;> simp_all [Bounds.upperAtMost, UpperHolds] <;> omega

def Bounds.assume (bounds : Bounds) (op : Comparison) (constant : Int) (truth : Bool) : Bounds :=
  match op, truth with
  | .lt, true | .ge, false => bounds.upperAtMost (constant - 1)
  | .lt, false | .ge, true => bounds.lowerAtLeast constant
  | .le, true | .gt, false => bounds.upperAtMost constant
  | .le, false | .gt, true => bounds.lowerAtLeast (constant + 1)
  | .eq, true | .ne, false => (bounds.lowerAtLeast constant).upperAtMost constant
  | .eq, false | .ne, true => bounds

theorem boundsAssumeSound (bounds : Bounds) (op : Comparison) (constant value : Int) (truth : Bool)
    (held : Holds bounds value) (branch : op.test value constant = truth) :
    Holds (bounds.assume op constant truth) value := by
  cases op <;> cases truth <;> simp only [Comparison.test, decide_eq_false_iff_not, decide_eq_true_eq] at branch
  all_goals first
    | exact held
    | exact lowerAtLeastSound bounds _ value held (by omega)
    | exact upperAtMostSound bounds _ value held (by omega)
    | exact upperAtMostSound _ _ value (lowerAtLeastSound bounds _ value held (by omega)) (by omega)

def Domain.assume (input : Domain) (op : Comparison) (constant : Int) (truth : Bool) : Domain :=
  Domain.unary (fun bounds => bounds.assume op constant truth) input

theorem assumeSound (input : Domain) (op : Comparison) (constant value : Int) (truth : Bool)
    (held : input.Holds value) (branch : op.test value constant = truth) :
    (input.assume op constant truth).Holds value := by
  have normalized := (normalizeSound input value).mpr held
  unfold Domain.assume Domain.unary
  cases inputCase : input.normalize with
  | unreachable => simp [inputCase, Domain.Holds] at normalized
  | bounded bounds =>
    simp only [inputCase, Domain.Holds] at normalized ⊢
    exact (normalizeSound (Domain.bounded (bounds.assume op constant truth)) value).mpr
      (boundsAssumeSound bounds op constant value truth normalized branch)

end ReductionBounds.IntegerSize
