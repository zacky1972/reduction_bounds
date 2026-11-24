namespace ReductionBounds.ProtocolConditions

open ReductionBounds.Protocol (Contract Event Runs)

structure DataSize where
  bytes : Nat
  structureSize : Nat
  deriving DecidableEq

def DataSize.Within (actual bound : DataSize) : Prop :=
  actual.bytes ≤ bound.bytes ∧ actual.structureSize ≤ bound.structureSize

instance (actual bound : DataSize) : Decidable (actual.Within bound) :=
  inferInstanceAs (Decidable (_ ∧ _))

structure Rule where
  before : String
  event : String
  data : List String
  integers : List String
  counts : List String

structure Observation where
  data : List (String × DataSize)
  integers : List (String × Int)

structure Spec where
  dataBounds : List (String × DataSize)
  integerBounds : List (String × ReductionBounds.IntegerSize.Bounds)
  countBounds : List (String × Nat)
  rules : List Rule

def findRule (spec : Spec) (before event : String) : Option Rule :=
  spec.rules.find? (fun rule => rule.before == before && rule.event == event)

def Spec.wellFormed (spec : Spec) (contract : Contract) : Bool :=
  decide (spec.dataBounds.map Prod.fst).Nodup &&
  decide (spec.integerBounds.map Prod.fst).Nodup &&
  decide (spec.countBounds.map Prod.fst).Nodup &&
  decide (spec.rules.map (fun rule => (rule.before, rule.event))).Nodup &&
  (spec.countBounds.lookup "total_events").isSome &&
  spec.integerBounds.all (fun entry => entry.2.magnitudeBits.isSome &&
    ReductionBounds.IntegerSize.contains entry.2 entry.2.witness) &&
  contract.transitions.all (fun edge => (findRule spec edge.before edge.event).isSome) &&
  spec.rules.all (fun rule =>
    contract.transitions.any (fun edge => edge.before == rule.before && edge.event == rule.event) &&
    decide rule.data.Nodup && decide rule.integers.Nodup && decide rule.counts.Nodup &&
    rule.data.all (fun name => (spec.dataBounds.lookup name).isSome) &&
    rule.integers.all (fun name => (spec.integerBounds.lookup name).isSome) &&
    rule.counts.all (fun name => name != "total_events" && (spec.countBounds.lookup name).isSome))

def Observation.wellFormed (observation : Observation) : Bool :=
  decide (observation.data.map Prod.fst).Nodup &&
  decide (observation.integers.map Prod.fst).Nodup

def DataAt (spec : Spec) (observation : Observation) (name : String) : Prop :=
  match spec.dataBounds.lookup name, observation.data.lookup name with
  | some bound, some actual => actual.Within bound
  | _, _ => False

instance (spec : Spec) (observation : Observation) (name : String) :
    Decidable (DataAt spec observation name) := by
  unfold DataAt
  cases spec.dataBounds.lookup name <;> cases observation.data.lookup name <;> infer_instance

def IntegerAt (spec : Spec) (observation : Observation) (name : String) : Prop :=
  match spec.integerBounds.lookup name, observation.integers.lookup name with
  | some bound, some value => ReductionBounds.IntegerSize.Holds bound value
  | _, _ => False

instance (spec : Spec) (observation : Observation) (name : String) :
    Decidable (IntegerAt spec observation name) := by
  unfold IntegerAt
  cases spec.integerBounds.lookup name <;> cases observation.integers.lookup name <;> infer_instance

def RowHolds (spec : Spec) (rule : Rule) (observation : Observation) : Prop :=
  observation.wellFormed = true ∧
    (∀ name ∈ rule.data, DataAt spec observation name) ∧
    (∀ name ∈ rule.integers, IntegerAt spec observation name)

instance (spec : Spec) (rule : Rule) (observation : Observation) :
    Decidable (RowHolds spec rule observation) := by
  unfold RowHolds
  infer_instance

def RowsHold (spec : Spec) (before : String) :
    List Event → List String → List Observation → Prop
  | [], [], [] => True
  | event :: rest, after :: states, observation :: observations =>
    match findRule spec before event.name with
    | none => False
    | some rule => RowHolds spec rule observation ∧ RowsHold spec after rest states observations
  | _, _, _ => False

def checkRows (spec : Spec) (before : String) :
    List Event → List String → List Observation → Bool
  | [], [], [] => true
  | event :: rest, after :: states, observation :: observations =>
    match findRule spec before event.name with
    | none => false
    | some rule => decide (RowHolds spec rule observation) && checkRows spec after rest states observations
  | _, _, _ => false

theorem checkRowsCorrect (spec : Spec) (before : String)
    (events : List Event) (states : List String) (observations : List Observation) :
    checkRows spec before events states observations = true ↔
      RowsHold spec before events states observations := by
  induction events generalizing before states observations with
  | nil => cases states <;> cases observations <;> simp [checkRows, RowsHold]
  | cons event rest ih =>
    cases states with
    | nil => cases observations <;> simp [checkRows, RowsHold]
    | cons after states =>
      cases observations with
      | nil => simp [checkRows, RowsHold]
      | cons observation observations =>
        cases found : findRule spec before event.name with
        | none => simp [checkRows, RowsHold, found]
        | some rule => simp [checkRows, RowsHold, found, ih]

def countFrom (spec : Spec) (before : String) (name : String) : List Event → List String → Nat
  | [], [] => 0
  | event :: rest, after :: states =>
    let amount := if name == "total_events" then 1 else
      match findRule spec before event.name with
      | none => 0
      | some rule => if rule.counts.contains name then 1 else 0
    amount + countFrom spec after name rest states
  | _, _ => 0

def CountsHold (spec : Spec) (before : String) (events : List Event) (states : List String) : Prop :=
  ∀ entry ∈ spec.countBounds, countFrom spec before entry.1 events states ≤ entry.2

instance (spec : Spec) (before : String) (events : List Event) (states : List String) :
    Decidable (CountsHold spec before events states) := by
  unfold CountsHold
  infer_instance

def checkConditions (contract : Contract) (spec : Spec) (events : List Event)
    (states : List String) (observations : List Observation) : Bool :=
  spec.wellFormed contract && ReductionBounds.Protocol.checkTrace contract events states &&
    checkRows spec contract.initial events states observations &&
    decide (CountsHold spec contract.initial events states)

theorem checkConditionsSound (contract : Contract) (spec : Spec) (events : List Event)
    (states : List String) (observations : List Observation)
    (accepted : checkConditions contract spec events states observations = true) :
    spec.wellFormed contract = true ∧ contract.wellFormed = true ∧
      Runs contract contract.initial events (ReductionBounds.Protocol.finish contract.initial states) ∧
      RowsHold spec contract.initial events states observations ∧
      CountsHold spec contract.initial events states := by
  have ⟨first, counts⟩ := Bool.and_eq_true_iff.mp accepted
  have ⟨first, rows⟩ := Bool.and_eq_true_iff.mp first
  have ⟨wellFormed, trace⟩ := Bool.and_eq_true_iff.mp first
  have checked := ReductionBounds.Protocol.checkTraceSound _ _ _ trace
  exact ⟨wellFormed, checked.1, checked.2,
    (checkRowsCorrect _ _ _ _ _).mp rows, of_decide_eq_true counts⟩

end ReductionBounds.ProtocolConditions
