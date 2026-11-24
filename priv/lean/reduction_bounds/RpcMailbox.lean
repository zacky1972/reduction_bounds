namespace ReductionBounds.RpcMailbox
open ReductionBounds.RpcTerm
open ReductionBounds.Mailbox

structure Counts where
  events : Nat := 0
  clientSends : Nat := 0
  serverSends : Nat := 0
  handlers : Nat := 0
  retries : Nat := 0
  deriving DecidableEq

def Counts.within (a b : Counts) : Bool :=
  a.events <= b.events && a.clientSends <= b.clientSends && a.serverSends <= b.serverSends &&
    a.handlers <= b.handlers && a.retries <= b.retries

structure Config where
  session : RpcProtocol.Session
  request : Term
  requestSize : Size
  responseSize : Size
  mailbox : Mailbox.Spec
  replyGuard : Guard
  limits : Counts

inductive Item where
  | protocol (name : String)
  | mailbox (action : Action)
  deriving DecidableEq

structure State where
  mailbox : Mailbox.State
  counts : Mailbox.Counts := {}
  protocolState : String := "idle"
  events : List String := []
  protocolCounts : Counts := {}
  deriving DecidableEq

def clauses (session : RpcProtocol.Session) (replyGuard : Guard) : List Clause :=
  [⟨"reply", .tuple3 (.literal (.atom "reply")) (.literal (.ref session.requestId)) .any, replyGuard⟩] ++
  match session.monitorId with
  | none => []
  | some id => [⟨"peer_down", .tuple5 (.literal (.atom "DOWN")) (.literal (.ref id)) (.literal (.atom "process")) .pid .any, .yes⟩]

def good (config : Config) : Bool :=
  config.mailbox.good && decide (config.mailbox.clauses = clauses config.session config.replyGuard) &&
  wellFormed config.request && within (measure config.request) config.requestSize &&
  matchPattern (.tuple3 (.literal (.atom "request")) (.literal (.ref config.session.requestId)) .any)
    config.request && config.limits.retries == 0

def waiting (name : String) : Bool :=
  ["awaiting_request", "request_available", "request_received", "reply_ready", "awaiting_reply",
   "reply_available"].contains name

def tick (counts : Counts) (event : String) : Counts :=
  {counts with
    events := counts.events + 1,
    clientSends := counts.clientSends + if event == "send_request" then 1 else 0,
    serverSends := counts.serverSends + if event == "send_reply" then 1 else 0,
    handlers := counts.handlers + if ["process_reply", "decode_error", "handle_peer_down", "handle_timeout"].contains event then 1 else 0}

def push (config : Config) (state : State) : List String → Option State
  | [] => some state
  | event :: rest => do
    let edge ← (RpcProtocol.contract config.session).transitions.find? (fun t =>
      t.before == state.protocolState && t.event == event)
    push config {state with
      protocolState := edge.after, events := state.events ++ [event],
      protocolCounts := tick state.protocolCounts event} rest

def project (config : Config) (state : State) : Action → Option State
  | .inspect => if state.mailbox.phase == .selected then do
      let term ← state.mailbox.selected
      if !(within (measure term) config.responseSize) then none else do
        let i ← state.mailbox.clause
        let clause ← config.mailbox.clauses[i]?
        if clause.kind == "reply" then push config state ["reply_arrived", "receive_reply"]
        else if clause.kind == "peer_down" then push config state ["peer_down", "handle_peer_down"]
        else none
    else push config state ["inspect_unrelated"]
  | .timeout => push config state ["timeout_elapsed"]
  | _ => some state

def step (config : Config) (state : State) : Item → Option State
  | .protocol event =>
    if ["monitor_peer", "prepare", "send_request", "request_arrived", "receive_request",
        "handle_request", "send_reply", "process_reply", "decode_error", "handle_timeout"].contains event
    then push config state [event] else none
  | .mailbox action => do
    let allowed := match action with
      | .arrive _ => true
      | .beginReceive => waiting state.protocolState && state.counts.receives == 0
      | _ => waiting state.protocolState
    if !allowed then none else do
      let (mailbox, delta) ← Mailbox.step config.mailbox state.mailbox action
      project config {state with mailbox := mailbox, counts := state.counts.add delta} action

def walk (config : Config) (state : State) : List Item → Option State
  | [] => some state
  | item :: rest => do
    let next ← step config state item
    if next.counts.within config.mailbox.limits && next.protocolCounts.within config.limits
    then walk config next rest else none

def run (config : Config) (queue : List Term) (items : List Item) : Option State :=
  if good config && queue.all (messageFits config.mailbox) then
    walk config {mailbox := Mailbox.initial queue} items else none

inductive Runs (config : Config) : State → List Item → State → Prop where
  | nil : Runs config state [] state
  | cons : step config before item = some next →
      next.counts.within config.mailbox.limits = true →
      next.protocolCounts.within config.limits = true →
      Runs config next rest final → Runs config before (item :: rest) final

theorem walkSound (config : Config) (state : State) (items : List Item) (final : State)
    (accepted : walk config state items = some final) : Runs config state items final := by
  induction items generalizing state with
  | nil => simp [walk] at accepted; subst final; exact .nil
  | cons item rest ih =>
    cases h : step config state item with
    | none => simp [walk, h] at accepted
    | some next =>
      have parts : (next.counts.within config.mailbox.limits = true ∧
          next.protocolCounts.within config.limits = true) ∧ walk config next rest = some final := by
        simpa [walk, h] using accepted
      exact .cons h parts.1.1 parts.1.2 (ih next parts.2)

theorem runSound (config : Config) (queue : List Term) (items : List Item) (final : State)
    (accepted : run config queue items = some final) :
    good config = true ∧ queue.all (messageFits config.mailbox) = true ∧
      Runs config {mailbox := Mailbox.initial queue} items final := by
  by_cases condition : (good config && queue.all (messageFits config.mailbox)) = true
  · have parts := Bool.and_eq_true_iff.mp condition
    exact ⟨parts.1, parts.2, walkSound _ _ _ _ (by simpa [run, condition] using accepted)⟩
  · simp [run, condition] at accepted

end ReductionBounds.RpcMailbox
