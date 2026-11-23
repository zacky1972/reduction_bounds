namespace ReductionBounds.Protocol

structure Event where
  name : String
  owner : Option String
  costUnit : Option String
  deriving DecidableEq

structure Transition where
  before : String
  event : String
  after : String
  deriving DecidableEq

structure Contract where
  participants : List (String × String)
  states : List String
  initial : String
  terminal : List String
  events : List Event
  transitions : List Transition

def eventMetadata (contract : Contract) (event : Event) : Bool :=
  match event.owner, event.costUnit with
  | none, none => true
  | some owner, some unit => contract.participants.contains (owner, unit)
  | _, _ => false

def Contract.wellFormed (contract : Contract) : Bool :=
  decide contract.states.Nodup &&
  decide (contract.participants.map Prod.fst).Nodup &&
  decide (contract.events.map Event.name).Nodup &&
  decide contract.terminal.Nodup &&
  decide (contract.transitions.map (fun edge => (edge.before, edge.event))).Nodup &&
  contract.states.contains contract.initial &&
  contract.terminal.all (fun state => contract.states.contains state) &&
  contract.events.all (eventMetadata contract) &&
  contract.transitions.all (fun edge =>
    contract.states.contains edge.before && contract.states.contains edge.after &&
    !(contract.terminal.contains edge.before) &&
    contract.events.any (fun event => event.name == edge.event))

def Allowed (contract : Contract) (before : String) (event : Event) (after : String) : Prop :=
  before ∈ contract.states ∧ before ∉ contract.terminal ∧ event ∈ contract.events ∧
    eventMetadata contract event = true ∧
    (⟨before, event.name, after⟩ : Transition) ∈ contract.transitions ∧ after ∈ contract.states

instance (contract : Contract) (before : String) (event : Event) (after : String) :
    Decidable (Allowed contract before event after) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _ ∧ _ ∧ _ ∧ _))

-- States supplies one successor for each event; it is checked, not trusted.
def checkFrom (contract : Contract) (before : String) : List Event → List String → Bool
  | [], [] => true
  | event :: rest, after :: states =>
    decide (Allowed contract before event after) && checkFrom contract after rest states
  | _, _ => false

def finish (before : String) : List String → String
  | [] => before
  | after :: states => finish after states

def checkTrace (contract : Contract) (events : List Event) (states : List String) : Bool :=
  contract.wellFormed && checkFrom contract contract.initial events states

inductive Runs (contract : Contract) : String → List Event → String → Prop where
  | nil : Runs contract state [] state
  | cons : Allowed contract before event after → Runs contract after rest final →
      Runs contract before (event :: rest) final

theorem checkFromSound (contract : Contract) (before : String)
    (events : List Event) (states : List String)
    (accepted : checkFrom contract before events states = true) :
    Runs contract before events (finish before states) := by
  induction events generalizing before states with
  | nil =>
    cases states with
    | nil => exact .nil
    | cons => simp [checkFrom] at accepted
  | cons event rest ih =>
    cases states with
    | nil => simp [checkFrom] at accepted
    | cons after states =>
      have parts := Bool.and_eq_true_iff.mp accepted
      exact .cons (of_decide_eq_true parts.1) (ih after states parts.2)

theorem checkTraceSound (contract : Contract) (events : List Event) (states : List String)
    (accepted : checkTrace contract events states = true) :
    contract.wellFormed = true ∧
      Runs contract contract.initial events (finish contract.initial states) := by
  have parts := Bool.and_eq_true_iff.mp accepted
  exact ⟨parts.1, checkFromSound contract contract.initial events states parts.2⟩

theorem Runs.preserves {contract : Contract} {before final : String} {events : List Event}
    (run : Runs contract before events final) (invariant : String → Prop)
    (initial : invariant before)
    (step : ∀ before event after, Allowed contract before event after →
      invariant before → invariant after) : invariant final := by
  induction run with
  | nil => exact initial
  | cons allowed _ ih => exact ih (step _ _ _ allowed initial)

theorem Runs.eventsValid {contract : Contract} {before final : String} {events : List Event}
    (run : Runs contract before events final) :
    ∀ event ∈ events, event ∈ contract.events ∧ eventMetadata contract event = true := by
  induction run with
  | nil => simp
  | @cons before event after rest final allowed _ ih =>
    intro candidate member
    rcases List.mem_cons.mp member with rfl | member
    · exact ⟨allowed.2.2.1, allowed.2.2.2.1⟩
    · exact ih candidate member

-- One occurrence cannot be assigned to two different participants.
theorem ownerExclusive (event : Event) (first second : String)
    (a : event.owner = some first) (b : event.owner = some second) : first = second :=
  Option.some.inj (a.symm.trans b)

end ReductionBounds.Protocol
