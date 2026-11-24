namespace ReductionBounds.RpcCompletion

/-- RPC control phases. Waiting without an item does not change the phase. -/
def phase : String → Nat
  | "idle" => 11
  | "monitored" => 10
  | "prepared" => 9
  | "awaiting_request" => 8
  | "request_available" => 7
  | "request_received" => 6
  | "reply_ready" => 5
  | "awaiting_reply" => 4
  | "reply_available" => 3
  | "reply_received" => 2
  | "timeout_observed" | "peer_down_observed" => 1
  | _ => 0

def protocolActions : List String :=
  ["monitor_peer", "prepare", "send_request", "request_arrived", "receive_request",
   "handle_request", "send_reply", "process_reply", "decode_error", "handle_timeout"]

def clientStates : List String :=
  ["idle", "monitored", "prepared", "reply_received", "timeout_observed", "peer_down_observed"]
def serverStates : List String := ["request_available", "request_received", "reply_ready"]
def responseStates : List String := ["awaiting_reply", "reply_available"]
def failureStates : List String :=
  ["timeout_observed", "peer_down_observed", "timed_out", "peer_terminated", "decode_failed"]

/-- The rank is checked against canonical RPC transitions, not Port transitions. -/
def Ranked (session : RpcProtocol.Session) : Prop :=
  (∀ edge ∈ (RpcProtocol.contract session).transitions, edge.event ∈ protocolActions →
    phase edge.after < phase edge.before) ∧
  (∀ s ∈ (RpcProtocol.contract session).states,
    s ∈ (RpcProtocol.contract session).terminal ∨ s ∈ clientStates ∨ s = "awaiting_request" ∨
      s ∈ serverStates ∨ s ∈ responseStates) ∧
  (∀ s ∈ (RpcProtocol.contract session).terminal, s = "complete" ∨ s ∈ failureStates)

instance (session : RpcProtocol.Session) : Decidable (Ranked session) := by
  unfold Ranked; infer_instance

theorem canonicalRanking (session : RpcProtocol.Session) : Ranked session := by
  unfold Ranked RpcProtocol.contract
  split <;> decide

theorem phaseBound (s : String) : phase s ≤ 11 := by
  unfold phase
  split <;> omega

/-- Remaining mailbox actions include arrivals, setup, inspections and timeout.
    Their allowance comes from the existing total mailbox step limit. -/
structure Configuration where
  model : RpcMailbox.State
  remaining : Nat
  deriving DecidableEq

def initial (c : RpcMailbox.Config) (queue : List RpcTerm.Term) : Configuration :=
  ⟨{mailbox := Mailbox.initial queue}, c.mailbox.limits.steps⟩

def Balanced (c : RpcMailbox.Config) (s : Configuration) : Prop :=
  s.remaining + s.model.counts.steps = c.mailbox.limits.steps

def rank (s : Configuration) : Nat := 12 * s.remaining + phase s.model.protocolState

def Known (c : RpcMailbox.Config) (s : Configuration) : Prop :=
  s.model.protocolState ∈ (RpcProtocol.contract c.session).states

def Control (c : RpcMailbox.Config) (before : Configuration) (item : RpcMailbox.Item)
    (after : Configuration) : Prop :=
  match item with
  | .protocol name => before.remaining = after.remaining ∧ name ∈ protocolActions ∧
      (⟨before.model.protocolState, name, after.model.protocolState⟩ : Protocol.Transition) ∈
        (RpcProtocol.contract c.session).transitions
  | .mailbox _ => before.remaining = after.remaining + 1

/-- Instrumented, checked mailbox execution; no free receive/timeout annotations. -/
def Advance (c : RpcMailbox.Config) (before : Configuration) (item : RpcMailbox.Item)
    (after : Configuration) : Prop :=
  RpcMailbox.step c before.model item = some after.model ∧
  after.model.counts.within c.mailbox.limits = true ∧
  after.model.protocolCounts.within c.limits = true ∧ Known c after ∧
  Balanced c before ∧ Balanced c after ∧ Control c before item after

instance (c : RpcMailbox.Config) (before after : Configuration) (item : RpcMailbox.Item) :
    Decidable (Advance c before item after) := by
  unfold Advance Known Balanced Control
  cases item <;> infer_instance

def advance (c : RpcMailbox.Config) (before : Configuration) (item : RpcMailbox.Item) :
    Option Configuration := do
  let model ← RpcMailbox.step c before.model item
  let after : Configuration := ⟨model, match item with
    | .protocol _ => before.remaining
    | .mailbox _ => before.remaining - 1⟩
  if Advance c before item after then some after else none

theorem advanceSound (c : RpcMailbox.Config) (before after : Configuration) (item : RpcMailbox.Item)
    (accepted : advance c before item = some after) : Advance c before item after := by
  cases h : RpcMailbox.step c before.model item with
  | none => simp [advance, h] at accepted
  | some model =>
    cases item <;> simp [advance, h] at accepted <;>
      rcases accepted with ⟨checked, rfl⟩ <;> exact checked

theorem advanceDecreases (c : RpcMailbox.Config) (checked : Ranked c.session)
    (before after : Configuration) (item : RpcMailbox.Item) (step : Advance c before item after) :
    rank after < rank before := by
  obtain ⟨_semantic, _mailbox, _protocol, _known, _balanceBefore, _balanceAfter, control⟩ := step
  cases item with
  | protocol name =>
    obtain ⟨same, allowed, edge⟩ := control
    have smaller := checked.1 _ edge allowed
    change phase after.model.protocolState < phase before.model.protocolState at smaller
    unfold rank
    omega
  | mailbox action =>
    have paid : before.remaining = after.remaining + 1 := control
    have bound := phaseBound after.model.protocolState
    unfold rank
    omega

inductive Moves (c : RpcMailbox.Config) : Configuration → List RpcMailbox.Item → Configuration → Prop where
  | nil : Moves c s [] s
  | cons : Advance c before item after → Moves c after rest final → Moves c before (item :: rest) final

def execute (c : RpcMailbox.Config) (s : Configuration) : List RpcMailbox.Item → Option Configuration
  | [] => some s
  | item :: rest => do
    let next ← advance c s item
    execute c next rest

theorem executeSound (c : RpcMailbox.Config) (s final : Configuration) (items : List RpcMailbox.Item)
    (checked : execute c s items = some final) : Moves c s items final := by
  induction items generalizing s with
  | nil => simp [execute] at checked; subst final; exact .nil
  | cons item rest ih =>
    cases h : advance c s item with
    | none => simp [execute, h] at checked
    | some next =>
      exact .cons (advanceSound _ _ _ _ h) (ih next (by simpa [execute, h] using checked))

theorem Moves.erased {c : RpcMailbox.Config} {before final : Configuration} {items : List RpcMailbox.Item}
    (run : Moves c before items final) : RpcMailbox.Runs c before.model items final.model := by
  induction run with
  | nil => exact .nil
  | cons step _ ih => exact .cons step.1 step.2.1 step.2.2.1 ih

theorem Moves.bounded {c : RpcMailbox.Config} (checked : Ranked c.session)
    {before final : Configuration} {items : List RpcMailbox.Item} (run : Moves c before items final) :
    items.length + rank final ≤ rank before := by
  induction run with
  | nil => simp
  | cons step _ ih =>
    have smaller := advanceDecreases c checked _ _ _ step
    simp only [List.length_cons]
    omega

/-- None is suspension/stuttering, not an active retry or an inspection. -/
structure Behavior (c : RpcMailbox.Config) (queue : List RpcTerm.Term) where
  config : Nat → Configuration
  item : Nat → Option RpcMailbox.Item
  starts : config 0 = initial c queue
  step : ∀ n, match item n with
    | none => config (n + 1) = config n
    | some action => Advance c (config n) action (config (n + 1))

def EventuallyActs {c : RpcMailbox.Config} {queue : List RpcTerm.Term} (b : Behavior c queue) (n : Nat) : Prop :=
  ∃ j, n ≤ j ∧ (b.item j).isSome = true

/-- Universal continuation assumptions respecting remaining limits, not evidence
    inferred from a finite example, a handler cost, or a timeout numeral. -/
structure Progress {c : RpcMailbox.Config} {queue : List RpcTerm.Term} (b : Behavior c queue) : Prop where
  client : ∀ n, (b.config n).model.protocolState ∈ clientStates → EventuallyActs b n
  request : ∀ n, (b.config n).model.protocolState = "awaiting_request" → EventuallyActs b n
  server : ∀ n, (b.config n).model.protocolState ∈ serverStates → EventuallyActs b n
  response : ∀ n, (b.config n).model.protocolState ∈ responseStates → EventuallyActs b n

theorem behaviorInvariant (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue)
    (n : Nat) : Known c (b.config n) := by
  induction n with
  | zero =>
    rw [b.starts]
    change "idle" ∈ (RpcProtocol.contract c.session).states
    unfold RpcProtocol.contract
    split <;> decide
  | succ n ih =>
    have step := b.step n
    cases h : b.item n with
    | none => simp only [h] at step; rw [step]; exact ih
    | some item => simp only [h] at step; exact step.2.2.2.1

theorem rankStep (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue) (n : Nat) :
    rank (b.config (n + 1)) ≤ rank (b.config n) := by
  have step := b.step n
  cases h : b.item n with
  | none => simp only [h] at step; rw [step]; exact Nat.le_refl _
  | some item => simp only [h] at step; exact Nat.le_of_lt (advanceDecreases c (canonicalRanking _) _ _ _ step)

theorem rankLater (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue)
    (n j : Nat) (later : n ≤ j) : rank (b.config j) ≤ rank (b.config n) := by
  induction later with
  | refl => exact Nat.le_refl _
  | @step j _ ih => exact Nat.le_trans (rankStep c queue b j) ih

theorem progressAt (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue)
    (progress : Progress b) (n : Nat)
    (unfinished : (b.config n).model.protocolState ∉ (RpcProtocol.contract c.session).terminal) :
    EventuallyActs b n := by
  have classified := ((canonicalRanking c.session).2.1 _ (behaviorInvariant c queue b n)).resolve_left unfinished
  rcases classified with client | request | server | response
  · exact progress.client n client
  · exact progress.request n request
  · exact progress.server n server
  · exact progress.response n response

theorem conditionalCompletion (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue)
    (progress : Progress b) : ∃ n, (b.config n).model.protocolState ∈ (RpcProtocol.contract c.session).terminal := by
  have finishes : ∀ k, ∀ n, rank (b.config n) = k →
      ∃ m, (b.config m).model.protocolState ∈ (RpcProtocol.contract c.session).terminal := by
    intro k
    induction k using Nat.strongRecOn with
    | ind k ih =>
      intro n same
      by_cases done : (b.config n).model.protocolState ∈ (RpcProtocol.contract c.session).terminal
      · exact ⟨n, done⟩
      · obtain ⟨j, later, active⟩ := progressAt c queue b progress n done
        have step := b.step j
        cases h : b.item j with
        | none => simp [h] at active
        | some item =>
          simp only [h] at step
          have decreases := Nat.lt_of_lt_of_le (advanceDecreases c (canonicalRanking _) _ _ _ step)
            (rankLater c queue b n j later)
          exact ih _ (by omega) (j + 1) rfl
  exact finishes _ 0 rfl

def activeCount {c : RpcMailbox.Config} {queue : List RpcTerm.Term} (b : Behavior c queue) : Nat → Nat
  | 0 => 0
  | n + 1 => activeCount b n + if (b.item n).isSome then 1 else 0

theorem eventCountBound (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue) (n : Nat) :
    activeCount b n + rank (b.config n) ≤ rank (initial c queue) := by
  induction n with
  | zero => simp [activeCount, b.starts]
  | succ n ih =>
    have step := b.step n
    cases h : b.item n with
    | none => simp only [h] at step; simp [activeCount, h, step]; exact ih
    | some item =>
      simp only [h] at step
      have smaller := advanceDecreases c (canonicalRanking _) _ _ _ step
      simp only [activeCount, h, Option.isSome_some, ite_true]
      omega

def NoFailure {c : RpcMailbox.Config} {queue : List RpcTerm.Term} (b : Behavior c queue) : Prop :=
  ∀ n item, b.item n = some item → (b.config (n + 1)).model.protocolState ∉ failureStates

theorem noFailureInvariant (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue)
    (safe : NoFailure b) (n : Nat) : (b.config n).model.protocolState ∉ failureStates := by
  induction n with
  | zero => rw [b.starts]; change "idle" ∉ failureStates; decide
  | succ n ih =>
    have step := b.step n
    cases h : b.item n with
    | none => simp only [h] at step; rw [step]; exact ih
    | some item => exact safe n item h

theorem successfulCompletion (c : RpcMailbox.Config) (queue : List RpcTerm.Term) (b : Behavior c queue)
    (progress : Progress b) (safe : NoFailure b) : ∃ n, (b.config n).model.protocolState = "complete" := by
  obtain ⟨n, terminal⟩ := conditionalCompletion c queue b progress
  exact ⟨n, ((canonicalRanking c.session).2.2 _ terminal).resolve_right (noFailureInvariant c queue b safe n)⟩

def stalledBehavior (c : RpcMailbox.Config) (queue : List RpcTerm.Term) : Behavior c queue where
  config := fun _ => initial c queue
  item := fun _ => none
  starts := rfl
  step := fun _ => rfl

theorem stalledNotComplete (c : RpcMailbox.Config) (queue : List RpcTerm.Term) :
    ¬ ∃ n, ((stalledBehavior c queue).config n).model.protocolState ∈ (RpcProtocol.contract c.session).terminal := by
  unfold stalledBehavior initial RpcProtocol.contract
  split <;> simp [RpcProtocol.monitoredContract, RpcProtocol.unmonitoredContract]

theorem stalledNoProgress (c : RpcMailbox.Config) (queue : List RpcTerm.Term) :
    ¬ Progress (stalledBehavior c queue) := by
  intro progress
  have active := progress.client 0 (by simp [stalledBehavior, initial, clientStates])
  simp [EventuallyActs, stalledBehavior] at active

end ReductionBounds.RpcCompletion
