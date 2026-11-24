namespace ReductionBounds.Mailbox
open ReductionBounds.RpcTerm

inductive Pattern where
  | any | pid | literal (value : Term)
  | cons (p0 : Pattern) (p1 : Pattern)
  | tuple2 (p0 : Pattern) (p1 : Pattern)
  | tuple3 (p0 : Pattern) (p1 : Pattern) (p2 : Pattern)
  | tuple5 (p0 : Pattern) (p1 : Pattern) (p2 : Pattern) (p3 : Pattern) (p4 : Pattern)
  deriving DecidableEq

def matchPattern : Pattern → Term → Bool
  | .any, _ => true
  | .pid, .pid _ => true
  | .literal a, b => decide (a = b)
  | .cons p0 p1, .cons v0 v1 => matchPattern p0 v0 && matchPattern p1 v1
  | .tuple2 p0 p1, .tuple2 v0 v1 => matchPattern p0 v0 && matchPattern p1 v1
  | .tuple3 p0 p1 p2, .tuple3 v0 v1 v2 => matchPattern p0 v0 && matchPattern p1 v1 && matchPattern p2 v2
  | .tuple5 p0 p1 p2 p3 p4, .tuple5 v0 v1 v2 v3 v4 => matchPattern p0 v0 && matchPattern p1 v1 && matchPattern p2 v2 && matchPattern p3 v3 && matchPattern p4 v4
  | _, _ => false

inductive Guard where
  | yes | no
  | isInteger (path : List Nat)
  | le (path : List Nat) (bound : Int)
  | ge (path : List Nat) (bound : Int)
  deriving DecidableEq

def guard (g : Guard) (term : Term) : Bool :=
  match g with
  | .yes => true
  | .no => false
  | .isInteger p => match atPath term p with | some (.integer _) => true | _ => false
  | .le p n => match atPath term p with | some (.integer v) => v <= n | _ => false
  | .ge p n => match atPath term p with | some (.integer v) => v >= n | _ => false

structure Clause where
  kind : String
  pattern : Pattern
  condition : Guard
  deriving DecidableEq

-- Clause and guard attempts, not machine instructions or recursive comparison cost.
def chooseFrom : List Clause → Term → Nat → Nat → Option Nat × Nat × Nat
  | [], _, i, g => (none, i, g)
  | c :: rest, term, i, g =>
    if matchPattern c.pattern term then
      if guard c.condition term then (some i, i + 1, g + 1)
      else chooseFrom rest term (i + 1) (g + 1)
    else chooseFrom rest term (i + 1) g

def choose (clauses : List Clause) (term : Term) := chooseFrom clauses term 0 0

structure Counts where
  steps : Nat := 0
  arrivals : Nat := 0
  receives : Nat := 0
  inspections : Nat := 0
  patterns : Nat := 0
  guards : Nat := 0
  deriving DecidableEq

def Counts.add (a b : Counts) : Counts := ⟨a.steps + b.steps, a.arrivals + b.arrivals, a.receives + b.receives, a.inspections + b.inspections, a.patterns + b.patterns, a.guards + b.guards⟩

def Counts.within (a b : Counts) : Bool := a.steps <= b.steps && a.arrivals <= b.arrivals && a.receives <= b.receives && a.inspections <= b.inspections && a.patterns <= b.patterns && a.guards <= b.guards

structure Spec where
  clauses : List Clause
  messageSize : Size
  limits : Counts
  timeout : Option Nat
  deriving DecidableEq

inductive Phase where
  | idle | searching | selected | timedOut
  deriving DecidableEq

structure State where
  queue : List Term
  cursor : Nat := 0
  phase : Phase := .idle
  selected : Option Term := none
  clause : Option Nat := none
  deriving DecidableEq

inductive Action where
  | arrive (term : Term)
  | beginReceive | inspect | timeout
  deriving DecidableEq

def initial (queue : List Term) : State := {queue := queue}
def messageFits (spec : Spec) (term : Term) : Bool :=
  wellFormed term && within (measure term) spec.messageSize

-- This logical side condition is not a second set of modeled inspections.
def rejectedPrefix (spec : Spec) (state : State) : Bool :=
  (state.queue.take state.cursor).all (fun t => decide ((choose spec.clauses t).1 = none))

def removeAt (queue : List Term) (cursor : Nat) : List Term :=
  queue.take cursor ++ queue.drop (cursor + 1)

def step (spec : Spec) (state : State) : Action → Option (State × Counts)
  | .arrive term => if messageFits spec term then
      some ({state with queue := state.queue ++ [term]}, {steps := 1, arrivals := 1}) else none
  | .beginReceive => if state.phase != .searching then
      some ({state with cursor := 0, phase := .searching, selected := none, clause := none},
        {steps := 1, receives := 1}) else none
  | .inspect => if state.phase == .searching && rejectedPrefix spec state then do
      let term ← state.queue[state.cursor]?
      let (clause, patterns, guards) := choose spec.clauses term
      let count : Counts := {steps := 1, inspections := 1, patterns := patterns, guards := guards}
      match clause with
      | none => some ({state with cursor := state.cursor + 1}, count)
      | some i => some (⟨removeAt state.queue state.cursor, 0, .selected, some term, some i⟩, count)
    else none
  | .timeout => if state.phase == .searching && spec.timeout.isSome &&
      state.cursor == state.queue.length && rejectedPrefix spec state then
      some ({state with phase := .timedOut, cursor := 0}, {steps := 1}) else none

def execute (spec : Spec) (state : State) : List Action → Option (State × Counts)
  | [] => some (state, {})
  | a :: rest => do
    let (next, delta) ← step spec state a
    let (final, counts) ← execute spec next rest
    pure (final, delta.add counts)

inductive Runs (spec : Spec) : State → List Action → State → Counts → Prop where
  | nil : Runs spec state [] state {}
  | cons : step spec before action = some (next, delta) →
      Runs spec next rest final counts →
      Runs spec before (action :: rest) final (delta.add counts)

theorem executeSound (spec : Spec) (state : State) (actions : List Action)
    (final : State) (counts : Counts) (accepted : execute spec state actions = some (final, counts)) :
    Runs spec state actions final counts := by
  induction actions generalizing state counts with
  | nil => simp [execute] at accepted; rcases accepted with ⟨rfl, rfl⟩; exact .nil
  | cons a rest ih =>
    cases h : step spec state a with
    | none => simp [execute, h] at accepted
    | some pair =>
      rcases pair with ⟨next, delta⟩
      cases tail : execute spec next rest with
      | none => simp [execute, h, tail] at accepted
      | some pair =>
        rcases pair with ⟨last, total⟩
        simp [execute, h, tail] at accepted
        rcases accepted with ⟨rfl, rfl⟩
        exact .cons h (ih next total tail)

theorem rejectedPrefixSound (spec : Spec) (state : State)
    (accepted : rejectedPrefix spec state = true) :
    ∀ term ∈ state.queue.take state.cursor, (choose spec.clauses term).1 = none := by
  intro term member
  exact of_decide_eq_true (List.all_eq_true.mp accepted term member)

theorem removalRetainsOrder (queue : List Term) (cursor : Nat) :
    removeAt queue cursor = queue.take cursor ++ queue.drop (cursor + 1) := rfl


def Pattern.valid : Pattern → Bool
  | .literal term => wellFormed term
  | .cons p0 p1 => Pattern.valid p0 && Pattern.valid p1
  | .tuple2 p0 p1 => Pattern.valid p0 && Pattern.valid p1
  | .tuple3 p0 p1 p2 => Pattern.valid p0 && Pattern.valid p1 && Pattern.valid p2
  | .tuple5 p0 p1 p2 p3 p4 => Pattern.valid p0 && Pattern.valid p1 && Pattern.valid p2 && Pattern.valid p3 && Pattern.valid p4
  | _ => true

def Guard.valid : Guard → Bool
  | .isInteger p | .le p _ | .ge p _ => p.all (· < 5)
  | _ => true

def Spec.good (spec : Spec) : Bool :=
  !(spec.clauses.isEmpty) && spec.clauses.all (fun c =>
    ["reply", "peer_down", "other"].contains c.kind && c.pattern.valid && c.condition.valid)

def check (spec : Spec) (queue : List Term) (actions : List Action)
    (final : State) (counts : Counts) : Bool :=
  spec.good && queue.all (messageFits spec) &&
    decide (execute spec (initial queue) actions = some (final, counts)) && counts.within spec.limits

theorem checkSound (spec : Spec) (queue : List Term) (actions : List Action)
    (final : State) (counts : Counts) (accepted : check spec queue actions final counts = true) :
    spec.good = true ∧ queue.all (messageFits spec) = true ∧
      Runs spec (initial queue) actions final counts ∧ counts.within spec.limits = true := by
  have outer := Bool.and_eq_true_iff.mp accepted
  have middle := Bool.and_eq_true_iff.mp outer.1
  have inner := Bool.and_eq_true_iff.mp middle.1
  exact ⟨inner.1, inner.2, executeSound _ _ _ _ _ (of_decide_eq_true middle.2), outer.2⟩

end ReductionBounds.Mailbox
