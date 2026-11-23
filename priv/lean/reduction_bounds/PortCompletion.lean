namespace ReductionBounds.PortCompletion

open ReductionBounds.Protocol (Contract Event Allowed)

structure Configuration where
  state : String
  rejections : Nat
  resumptions : Nat
  inspections : Nat
  deriving DecidableEq

def phase : String → Nat
  | "idle" => 9
  | "rejected" => 8
  | "prepared" | "submission_resumed" => 7
  | "submission_wait" => 6
  | "awaiting_response" => 4
  | "response_available" => 3
  | "response_received" => 2
  | "closure_observed" | "timeout_observed" => 1
  | _ => 0

def rejection (name : String) : Nat := if name = "submit_rejected" then 1 else 0

def resumption (name : String) : Nat := if name = "resume_submission" then 1 else 0

def inspection (name : String) : Nat :=
  if name = "inspect_message" ∨ name = "receive_response" then 1 else 0

def spent (name : String) : Nat := rejection name + resumption name + inspection name

def rank (s : Configuration) : Nat :=
  10 * (s.rejections + s.resumptions + s.inspections) + phase s.state

def Advance (contract : Contract) (before : Configuration) (event : Event)
    (after : Configuration) : Prop :=
  Allowed contract before.state event after.state ∧
  before.rejections = after.rejections + rejection event.name ∧
  before.resumptions = after.resumptions + resumption event.name ∧
  before.inspections = after.inspections + inspection event.name

instance (contract : Contract) (before : Configuration) (event : Event) (after : Configuration) :
    Decidable (Advance contract before event after) := by unfold Advance; infer_instance

def Ranked (contract : Contract) : Prop :=
  (∀ edge ∈ contract.transitions, phase edge.after ≤ 9 ∧
    (0 < spent edge.event ∨ phase edge.after < phase edge.before)) ∧
  (∀ state ∈ contract.states, state ∈ contract.terminal ∨
    state ∈ ["idle", "prepared", "submission_resumed", "submission_wait", "rejected",
      "awaiting_response", "response_available", "response_received", "closure_observed", "timeout_observed"])

instance (contract : Contract) : Decidable (Ranked contract) := by unfold Ranked; infer_instance

theorem advanceDecreases (contract : Contract) (checked : Ranked contract)
    (before after : Configuration) (event : Event) (step : Advance contract before event after) :
    rank after < rank before := by
  obtain ⟨allowed, rejected, resumed, inspected⟩ := step
  have edge := checked.1 _ allowed.2.2.2.2.1
  change phase after.state ≤ 9 ∧
    (0 < spent event.name ∨ phase after.state < phase before.state) at edge
  rcases edge.2 with paid | phaseDecrease
  · unfold rank
    unfold spent at paid
    omega
  · unfold rank
    omega

inductive Moves (contract : Contract) : Configuration → List Event → Configuration → Prop where
  | nil : Moves contract s [] s
  | cons : Advance contract before event after → Moves contract after rest final →
      Moves contract before (event :: rest) final

def finish (before : Configuration) : List Configuration → Configuration
  | [] => before
  | after :: rest => finish after rest

def checkMoves (contract : Contract) (before : Configuration) : List Event → List Configuration → Bool
  | [], [] => true
  | event :: rest, after :: states => decide (Advance contract before event after) && checkMoves contract after rest states
  | _, _ => false

theorem checkMovesSound (contract : Contract) (before : Configuration)
    (events : List Event) (states : List Configuration)
    (checked : checkMoves contract before events states = true) :
    Moves contract before events (finish before states) := by
  induction events generalizing before states with
  | nil => cases states <;> simp [checkMoves] at checked; exact .nil
  | cons event rest ih =>
    cases states with
    | nil => simp [checkMoves] at checked
    | cons after states =>
      have parts := Bool.and_eq_true_iff.mp checked
      exact .cons (of_decide_eq_true parts.1) (ih after states parts.2)

theorem Moves.erased {contract : Contract} {before final : Configuration} {events : List Event}
    (run : Moves contract before events final) :
    ReductionBounds.Protocol.Runs contract before.state events final.state := by
  induction run with
  | nil => exact .nil
  | cons step _ ih => exact .cons step.1 ih

theorem Moves.bounded {contract : Contract} (checked : Ranked contract)
    {before final : Configuration} {events : List Event} (run : Moves contract before events final) :
    events.length + rank final ≤ rank before := by
  induction run with
  | nil => simp
  | cons step _ ih =>
    have smaller := advanceDecreases contract checked _ _ _ step
    simp only [List.length_cons]
    omega

def acceptedStates : List String := ["awaiting_response", "response_available", "response_received",
  "closure_observed", "timeout_observed", "complete", "failed", "closed", "timed_out", "decode_failed"]

def submissionEvents : List String := ["submit_accepted", "submit_rejected", "submit_suspended", "retry"]

def PostAcceptanceSafe (contract : Contract) : Prop :=
  ∀ edge ∈ contract.transitions, edge.before ∈ acceptedStates →
    edge.after ∈ acceptedStates ∧ edge.event ∉ submissionEvents

instance (contract : Contract) : Decidable (PostAcceptanceSafe contract) := by
  unfold PostAcceptanceSafe; infer_instance

theorem acceptedPreserves (contract : Contract) (checked : PostAcceptanceSafe contract)
    (before final : String) (events : List Event)
    (run : ReductionBounds.Protocol.Runs contract before events final)
    (accepted : before ∈ acceptedStates) : final ∈ acceptedStates := by
  apply run.preserves (fun state => state ∈ acceptedStates) accepted
  intro before event after allowed known
  exact (checked _ allowed.2.2.2.2.1 known).1

theorem noRetransmission (contract : Contract) (checked : PostAcceptanceSafe contract)
    (before final : String) (events : List Event)
    (run : ReductionBounds.Protocol.Runs contract before events final)
    (accepted : before ∈ acceptedStates) : ∀ event ∈ events, event.name ∉ submissionEvents := by
  induction run with
  | nil => simp
  | cons step _ ih =>
    have safe := checked _ step.2.2.2.2.1 accepted
    intro event member
    rcases List.mem_cons.mp member with rfl | member
    · exact safe.2
    · exact ih safe.1 event member

-- Idle time is not an active protocol event. Terminal states can remain idle.
structure Behavior (contract : Contract) where
  config : Nat → Configuration
  event : Nat → Option Event
  initial : (config 0).state = contract.initial
  step : ∀ n, match event n with
    | none => config (n + 1) = config n
    | some event => Advance contract (config n) event (config (n + 1))

def EventuallyActs {contract : Contract} (behavior : Behavior contract) (n : Nat) : Prop :=
  ∃ j, n ≤ j ∧ (behavior.event j).isSome = true

-- These are environment and scheduling hypotheses, not facts inferred from costs.
structure Progress {contract : Contract} (behavior : Behavior contract) : Prop where
  caller : ∀ n, (behavior.config n).state ∈ ["idle", "rejected", "response_available",
    "response_received", "closure_observed", "timeout_observed"] → EventuallyActs behavior n
  submission : ∀ n, (behavior.config n).state ∈ ["prepared", "submission_resumed"] → EventuallyActs behavior n
  resumption : ∀ n, (behavior.config n).state = "submission_wait" → EventuallyActs behavior n
  response : ∀ n, (behavior.config n).state = "awaiting_response" → EventuallyActs behavior n

theorem behaviorInvariant (contract : Contract) (behavior : Behavior contract)
    (initial : contract.initial ∈ contract.states) (n : Nat) :
    (behavior.config n).state ∈ contract.states := by
  induction n with
  | zero => simpa [behavior.initial] using initial
  | succ n ih =>
    have step := behavior.step n
    cases event : behavior.event n with
    | none => simp only [event] at step; rw [step]; exact ih
    | some event => simp only [event] at step; exact step.1.2.2.2.2.2

theorem rankStep (contract : Contract) (checked : Ranked contract) (behavior : Behavior contract) (n : Nat) :
    rank (behavior.config (n + 1)) ≤ rank (behavior.config n) := by
  have step := behavior.step n
  cases event : behavior.event n with
  | none => simp only [event] at step; rw [step]; exact Nat.le_refl _
  | some event => simp only [event] at step; exact Nat.le_of_lt (advanceDecreases contract checked _ _ _ step)

theorem rankLater (contract : Contract) (checked : Ranked contract) (behavior : Behavior contract)
    (n j : Nat) (later : n ≤ j) : rank (behavior.config j) ≤ rank (behavior.config n) := by
  induction later with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans (rankStep contract checked behavior j) ih

theorem progressAt (contract : Contract) (checked : Ranked contract) (behavior : Behavior contract)
    (progress : Progress behavior) (n : Nat) (known : (behavior.config n).state ∈ contract.states)
    (unfinished : (behavior.config n).state ∉ contract.terminal) : EventuallyActs behavior n := by
  have cases := (checked.2 _ known).resolve_left unfinished
  simp only [List.mem_cons, List.not_mem_nil, or_false] at cases
  rcases cases with h | h | h | h | h | h | h | h | h | h
  · exact progress.caller n (by simp [h])
  · exact progress.submission n (by simp [h])
  · exact progress.submission n (by simp [h])
  · exact progress.resumption n h
  · exact progress.caller n (by simp [h])
  · exact progress.response n h
  all_goals exact progress.caller n (by simp [h])

theorem conditionalCompletion (contract : Contract) (checked : Ranked contract)
    (initial : contract.initial ∈ contract.states) (behavior : Behavior contract)
    (progress : Progress behavior) : ∃ n, (behavior.config n).state ∈ contract.terminal := by
  have finishes : ∀ k, ∀ n, rank (behavior.config n) = k →
      ∃ m, (behavior.config m).state ∈ contract.terminal := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n same
      by_cases done : (behavior.config n).state ∈ contract.terminal
      · exact ⟨n, done⟩
      · obtain ⟨j, later, active⟩ := progressAt contract checked behavior progress n
          (behaviorInvariant contract behavior initial n) done
        have step := behavior.step j
        cases event : behavior.event j with
        | none => simp [event] at active
        | some event =>
          simp only [event] at step
          have decreases := Nat.lt_of_lt_of_le (advanceDecreases contract checked _ _ _ step)
            (rankLater contract checked behavior n j later)
          exact ih _ (by omega) (j + 1) rfl
  exact finishes _ 0 rfl

def activeCount {contract : Contract} (behavior : Behavior contract) : Nat → Nat
  | 0 => 0
  | n + 1 => activeCount behavior n + if (behavior.event n).isSome then 1 else 0

theorem eventCountBound (contract : Contract) (checked : Ranked contract)
    (behavior : Behavior contract) (n : Nat) :
    activeCount behavior n + rank (behavior.config n) ≤ rank (behavior.config 0) := by
  induction n with
  | zero => simp [activeCount]
  | succ n ih =>
    have step := behavior.step n
    cases event : behavior.event n with
    | none => simp only [event] at step; simp [activeCount, event, step]; exact ih
    | some event =>
      simp only [event] at step
      have decreases := advanceDecreases contract checked _ _ _ step
      simp only [activeCount, event, Option.isSome_some, ite_true]
      omega

def failureStates : List String := ["failed", "closed", "timed_out", "decode_failed"]

def failureEvents : List String := ["return_rejection", "handle_closure", "handle_timeout", "decode_error"]

def SuccessSpec (contract : Contract) : Prop :=
  contract.initial ∉ failureStates ∧
  (∀ edge ∈ contract.transitions, edge.after ∈ failureStates → edge.event ∈ failureEvents) ∧
  (∀ state ∈ contract.terminal, state = "complete" ∨ state ∈ failureStates)

instance (contract : Contract) : Decidable (SuccessSpec contract) := by unfold SuccessSpec; infer_instance

def NoFailure {contract : Contract} (behavior : Behavior contract) : Prop :=
  ∀ n event, behavior.event n = some event → event.name ∉ failureEvents

theorem noFailureInvariant (contract : Contract) (checked : SuccessSpec contract)
    (behavior : Behavior contract) (safe : NoFailure behavior) (n : Nat) :
    (behavior.config n).state ∉ failureStates := by
  induction n with
  | zero => simpa [behavior.initial] using checked.1
  | succ n ih =>
    have step := behavior.step n
    cases event : behavior.event n with
    | none => simp only [event] at step; rw [step]; exact ih
    | some action =>
      simp only [event] at step
      intro failed
      exact safe n action event (checked.2.1 _ step.1.2.2.2.2.1 failed)

-- Success additionally excludes rejection, closure, timeout and decoding failure outcomes.
theorem successfulCompletion (contract : Contract) (checked : Ranked contract)
    (successSpec : SuccessSpec contract) (initial : contract.initial ∈ contract.states)
    (behavior : Behavior contract) (progress : Progress behavior) (safe : NoFailure behavior) :
    ∃ n, (behavior.config n).state = "complete" := by
  obtain ⟨n, done⟩ := conditionalCompletion contract checked initial behavior progress
  have outcome := successSpec.2.2 _ done
  exact ⟨n, outcome.resolve_right (noFailureInvariant contract successSpec behavior safe n)⟩

def stalledBehavior (contract : Contract) (initial : Configuration)
    (starts : initial.state = contract.initial) : Behavior contract where
  config := fun _ => initial
  event := fun _ => none
  initial := starts
  step := fun _ => rfl

theorem stalledNotComplete (contract : Contract) (initial : Configuration)
    (starts : initial.state = contract.initial) (unfinished : initial.state ∉ contract.terminal) :
    ¬ ∃ n, ((stalledBehavior contract initial starts).config n).state ∈ contract.terminal := by
  simpa [stalledBehavior] using unfinished

end ReductionBounds.PortCompletion
