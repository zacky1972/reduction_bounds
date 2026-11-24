namespace ReductionBounds.RpcSource

abbrev Value := RpcTerm.Term
abbrev Env := String → Value

def bind (env : Env) (name : String) (value : Value) : Env :=
  fun key => if key = name then value else env key

inductive Arg where
  | variable (name : String)
  | literal (value : Value)
  | tuple3 (a b c : Arg)
  deriving DecidableEq

def Arg.eval (env : Env) : Arg → Value
  | .variable name => env name
  | .literal value => value
  | .tuple3 a b c => .tuple3 (a.eval env) (b.eval env) (c.eval env)

def Arg.budget : Arg → Nat
  | .tuple3 a b c => 1 + a.budget + b.budget + c.budget
  | _ => 1

structure Call where
  moduleName : String
  functionName : String
  args : List Arg
  deriving DecidableEq

structure Invocation where
  moduleName : String
  functionName : String
  args : List Value
  result : Value
  events : List RpcProtocol.Event

abbrev External := String → String → List Value → Value → List RpcProtocol.Event → Prop

def Invokes (external : External) (call : Call) (env : Env) (inv : Invocation) : Prop :=
  inv.moduleName = call.moduleName ∧ inv.functionName = call.functionName ∧
  inv.args = call.args.map (Arg.eval env) ∧
    external inv.moduleName inv.functionName inv.args inv.result inv.events

/-- Reified normal Core blocks; the excluded compiler match-failure arm is
    outside the explicit helper result contract, not silently treated as return. -/
inductive Core where
  | ret (value : Arg)
  | letValue (binder : String) (value : Arg) (body : Core)
  | seqCall (call : Call) (body : Core)
  | replyCase (call : Call) (binder : String) (order : List String) (reply timeout : Core)
  | tailCall (call : Call)
  deriving DecidableEq

def Core.budget : Core → Nat
  | .ret _ => 1
  | .letValue _ value body => 2 + value.budget + body.budget
  | .seqCall call body => 1 + call.args.length + body.budget
  | .replyCase call _ _ a b => 6 + call.args.length + a.budget + b.budget
  | .tailCall call => 1 + call.args.length

inductive Evaluates (external : External) : Core → Env → Value → List Invocation → Nat → Prop where
  | ret : Evaluates external (.ret value) env (value.eval env) [] 1
  | letValue : Evaluates external body (bind env binder (arg.eval env)) value calls work →
      Evaluates external (.letValue binder arg body) env value calls (2 + arg.budget + work)
  | seqCall : Invokes external call env inv → Evaluates external body env value calls work →
      Evaluates external (.seqCall call body) env value (inv :: calls) (1 + call.args.length + work)
  | replyData : Invokes external call env inv → inv.result = .tuple2 (.atom "reply") payload →
      Evaluates external a (bind env binder payload) value calls work →
      Evaluates external (.replyCase call binder order a b) env value (inv :: calls) (6 + call.args.length + work)
  | replyTimeout : Invokes external call env inv → inv.result = .atom "timeout" →
      Evaluates external b env value calls work →
      Evaluates external (.replyCase call binder order a b) env value (inv :: calls) (6 + call.args.length + work)
  | tailCall : Invokes external call env inv →
      Evaluates external (.tailCall call) env inv.result [inv] (1 + call.args.length)

theorem localBound {external core env value calls work}
    (run : Evaluates external core env value calls work) : work ≤ core.budget := by
  induction run <;> simp_all [Core.budget] <;> omega

inductive Role where | send | reply | decode deriving DecidableEq
abbrev Registry := Role → String × String

def RegistryValid (registry : Registry) : Prop :=
  registry .send = ("erlang", "send") ∧ ([Role.send, .reply, .decode].map registry).Nodup
instance (registry : Registry) : Decidable (RegistryValid registry) := by
  unfold RegistryValid; infer_instance

def Registered (registry : Registry) (role : Role) (call : Call) : Prop :=
  registry role = (call.moduleName, call.functionName) ∧
  call.args.length = (match role with | .send => 2 | .reply => 3 | .decode => 1)
instance (registry : Registry) (role : Role) (call : Call) : Decidable (Registered registry role call) := by
  unfold Registered; infer_instance

structure Context where
  state : String
  server : String
  token : String
  input : String
  timeout : String
  request : String
  data : String

def clientEvent (s : RpcProtocol.Session) (name : String) : RpcProtocol.Event :=
  ⟨⟨name, some "client", some "client_work"⟩,
    if RpcProtocol.requestEvents.contains name then some s.requestId else none, none⟩

def Segment (s : RpcProtocol.Session) (before : String) (events : List RpcProtocol.Event) (after : String) : Prop :=
  Protocol.Runs (RpcProtocol.contract s) before (events.map RpcProtocol.Event.protocol) after ∧
  ∀ event ∈ events, RpcProtocol.Correlated s event

def PureStep (s : RpcProtocol.Session) (before name after : String) : Prop :=
  Protocol.Allowed (RpcProtocol.contract s) before (clientEvent s name).protocol after ∧
    RpcProtocol.Correlated s (clientEvent s name)
instance (s : RpcProtocol.Session) (before name after : String) : Decidable (PureStep s before name after) := by
  unfold PureStep; infer_instance

theorem singleSegment {s before name after} (step : PureStep s before name after) :
    Segment s before [clientEvent s name] after := by
  refine ⟨.cons step.1 .nil, ?_⟩
  intro event member
  simp only [List.mem_cons, List.not_mem_nil, or_false] at member
  subst event
  exact step.2

theorem appendSegment {s before middle final first second}
    (a : Segment s before first middle) (b : Segment s middle second final) :
    Segment s before (first ++ second) final := by
  have appendRuns {x y z : String} {xs ys : List Protocol.Event}
      (p : Protocol.Runs (RpcProtocol.contract s) x xs y)
      (q : Protocol.Runs (RpcProtocol.contract s) y ys z) :
      Protocol.Runs (RpcProtocol.contract s) x (xs ++ ys) z := by
    induction p with
    | nil => exact q
    | cons step _ ih => exact .cons step (ih q)
  refine ⟨by simpa using appendRuns a.1 b.1, ?_⟩
  intro event member
  rcases List.mem_append.mp member with h | h
  · exact a.2 event h
  · exact b.2 event h

def timeoutValue : Option Nat → Value
  | none => .atom "infinity"
  | some n => .integer (Int.ofNat n)

/-- Applicability to the abstract model inputs, not a verified runtime PID/ref mapping. -/
structure InputsHold (c : RpcMailbox.Config) (ctx : Context) (env : Env) : Prop where
  request : .tuple3 (.atom "request") (env ctx.token) (env ctx.input) = c.request
  server : ∃ peer, env ctx.server = .pid peer
  timeout : env ctx.timeout = timeoutValue c.mailbox.timeout

def Deterministic (s : RpcProtocol.Session) : Prop :=
  ∀ a ∈ (RpcProtocol.contract s).transitions, ∀ b ∈ (RpcProtocol.contract s).transitions,
    a.before = b.before → a.event = b.event → a.after = b.after
instance (s : RpcProtocol.Session) : Decidable (Deterministic s) := by
  unfold Deterministic; infer_instance

theorem canonicalDeterministic (s : RpcProtocol.Session) : Deterministic s := by
  unfold Deterministic RpcProtocol.contract
  split <;> decide

theorem finalUnique {s before events a b}
    (first : Protocol.Runs (RpcProtocol.contract s) before events a)
    (second : Protocol.Runs (RpcProtocol.contract s) before events b) : a = b := by
  induction first with
  | nil => cases second; rfl
  | cons allowed _ ih =>
    cases second with
    | cons other rest =>
      have same := canonicalDeterministic s _ allowed.2.2.2.2.1 _ other.2.2.2.2.1 rfl rfl
      cases same
      exact ih rest

inductive Program where
  | prepare (binder : String) (value : Arg) (body : Program)
  | send (call : Call) (body : Program)
  | reply (call : Call) (binder : String) (reply timeout : Program)
  | decode (call : Call)
  | timeout

/-- Timeout constants are checked against the mailbox model, rather than used
    as progress assumptions or local computation budgets. -/
def ReplyArgs (ctx : Context) (timeout : Value) (call : Call) : Prop :=
  call.args = [.variable ctx.server, .variable ctx.token, .variable ctx.timeout] ∨
  call.args = [.variable ctx.server, .variable ctx.token, .literal timeout]
instance (ctx : Context) (timeout : Value) (call : Call) : Decidable (ReplyArgs ctx timeout call) := by
  unfold ReplyArgs; infer_instance

inductive Connect (s : RpcProtocol.Session) (registry : Registry) (timeout : Value) :
    Core → Context → Program → Prop where
  | prepare : value = .tuple3 (.literal (.atom "request")) (.variable ctx.token) (.variable ctx.input) →
      binder ∉ [ctx.server, ctx.token, ctx.input, ctx.timeout] → ctx.state = "idle" →
      PureStep s ctx.state "prepare" "prepared" →
      Connect s registry timeout body {ctx with state := "prepared", request := binder} program →
      Connect s registry timeout (.letValue binder value body) ctx (.prepare binder value program)
  | send : Registered registry .send call → call.args = [.variable ctx.server, .variable ctx.request] →
      ctx.state = "prepared" →
      Connect s registry timeout body {ctx with state := "awaiting_request"} program →
      Connect s registry timeout (.seqCall call body) ctx (.send call program)
  | reply : Registered registry .reply call → ReplyArgs ctx timeout call → ctx.state = "awaiting_request" →
      order.Perm ["reply", "timeout"] → binder ∉ [ctx.server, ctx.token, ctx.input, ctx.timeout, ctx.request] →
      Connect s registry timeout a {ctx with state := "reply_received", data := binder} pa →
      Connect s registry timeout b {ctx with state := "timeout_observed"} pb →
      Connect s registry timeout (.replyCase call binder order a b) ctx (.reply call binder pa pb)
  | decode : Registered registry .decode call → call.args = [.variable ctx.data] → ctx.state = "reply_received" →
      Connect s registry timeout (.tailCall call) ctx (.decode call)
  | timeout : ctx.state = "timeout_observed" → PureStep s ctx.state "handle_timeout" "timed_out" →
      Connect s registry timeout (.ret (.literal (.atom "timeout"))) ctx .timeout

inductive Executes (s : RpcProtocol.Session) (external : External) :
    Program → Env → Value → List Invocation → Nat → List RpcProtocol.Event → Prop where
  | prepare : Executes s external body (bind env binder (arg.eval env)) value calls work trace →
      Executes s external (.prepare binder arg body) env value calls (2 + arg.budget + work)
        (clientEvent s "prepare" :: trace)
  | send : Invokes external call env inv → Executes s external body env value calls work trace →
      Executes s external (.send call body) env value (inv :: calls) (1 + call.args.length + work) (inv.events ++ trace)
  | replyData : Invokes external call env inv → inv.result = .tuple2 (.atom "reply") payload →
      Executes s external a (bind env binder payload) value calls work trace →
      Executes s external (.reply call binder a b) env value (inv :: calls) (6 + call.args.length + work) (inv.events ++ trace)
  | replyTimeout : Invokes external call env inv → inv.result = .atom "timeout" →
      Executes s external b env value calls work trace →
      Executes s external (.reply call binder a b) env value (inv :: calls) (6 + call.args.length + work) (inv.events ++ trace)
  | decode : Invokes external call env inv →
      Executes s external (.decode call) env inv.result [inv] (1 + call.args.length) inv.events
  | timeout : Executes s external .timeout env (.atom "timeout") [] 1 [clientEvent s "handle_timeout"]

theorem sourceAgreement {s registry timeout core ctx program}
    (connected : Connect s registry timeout core ctx program) {external env value calls work}
    (run : Evaluates external core env value calls work) :
    ∃ trace, Executes s external program env value calls work trace := by
  induction connected generalizing env value calls work with
  | prepare _ _ _ _ _ ih =>
    cases run with | letValue rest => obtain ⟨trace, modeled⟩ := ih rest; exact ⟨_, .prepare modeled⟩
  | send _ _ _ _ ih =>
    cases run with | seqCall invoked rest => obtain ⟨trace, modeled⟩ := ih rest; exact ⟨_, .send invoked modeled⟩
  | reply _ _ _ _ _ _ _ ia ib =>
    cases run with
    | replyData invoked same rest => obtain ⟨trace, modeled⟩ := ia rest; exact ⟨_, .replyData invoked same modeled⟩
    | replyTimeout invoked same rest => obtain ⟨trace, modeled⟩ := ib rest; exact ⟨_, .replyTimeout invoked same modeled⟩
  | decode => cases run with | tailCall invoked => exact ⟨_, .decode invoked⟩
  | timeout => cases run; exact ⟨_, .timeout⟩

def ReplyData (c : RpcMailbox.Config) (registry : Registry) (calls : List Invocation)
    (state : RpcMailbox.State) : Prop :=
  ∀ inv ∈ calls, (inv.moduleName, inv.functionName) = registry .reply →
    match inv.result with
    | .tuple2 (.atom "reply") payload =>
        state.mailbox.selected = some (.tuple3 (.atom "reply") (.ref c.session.requestId) payload)
    | .atom "timeout" => state.mailbox.phase = .timedOut
    | _ => False

def callBefore : Role → String
  | .send => "prepared" | .reply => "awaiting_request" | .decode => "reply_received"
def callAfter : Role → Value → String
  | .send, _ => "awaiting_request"
  | .reply, .tuple2 (.atom "reply") _ => "reply_received"
  | .reply, _ => "timeout_observed"
  | .decode, value => if value = .atom "decode_error" then "decode_failed" else "complete"

def ResultAllowed : Role → List Value → Value → Prop
  | .send, args, value => args[1]? = some value
  | .reply, _, value => (∃ payload, value = .tuple2 (.atom "reply") payload) ∨ value = .atom "timeout"
  | .decode, _, _ => True

/-- Helper/primitive result and finite trace contracts, not verified bodies,
    totality, mailbox implementations or scheduler/delivery guarantees. -/
def Contracts (s : RpcProtocol.Session) (registry : Registry) (external : External) : Prop :=
  ∀ role call env inv, Registered registry role call → Invokes external call env inv →
    ResultAllowed role inv.args inv.result ∧ Segment s (callBefore role) inv.events (callAfter role inv.result)

def emptyExternal : External := fun _ _ _ _ _ => False

theorem emptyContracts (s : RpcProtocol.Session) (registry : Registry) :
    Contracts s registry emptyExternal := by
  intro role call env inv _registered invoked
  exact False.elim invoked.2.2.2

theorem modelSafe {s registry timeout core ctx program}
    (connected : Connect s registry timeout core ctx program) {external env value calls work trace}
    (run : Executes s external program env value calls work trace)
    (contracts : Contracts s registry external)
    (terminals : ∀ value, callAfter .decode value ∈ (RpcProtocol.contract s).terminal)
    (timedOut : "timed_out" ∈ (RpcProtocol.contract s).terminal) :
    ∃ final, Segment s ctx.state trace final ∧ final ∈ (RpcProtocol.contract s).terminal := by
  induction connected generalizing env value calls work trace with
  | prepare _ _ _ step _ ih =>
    cases run with
    | prepare rest =>
      obtain ⟨final, suffix, terminal⟩ := ih rest
      exact ⟨final, appendSegment (singleSegment step) suffix, terminal⟩
  | send registered _ state _ ih =>
    cases run with
    | send invoked rest =>
      obtain ⟨final, suffix, terminal⟩ := ih rest
      have head := (contracts .send _ _ _ registered invoked).2
      simp only [callBefore, callAfter] at head
      exact ⟨final, state ▸ appendSegment head suffix, terminal⟩
  | reply registered _ state _ _ _ _ ia ib =>
    cases run with
    | replyData invoked same rest =>
      obtain ⟨final, suffix, terminal⟩ := ia rest
      have head := (contracts .reply _ _ _ registered invoked).2
      simp [callBefore, callAfter, same] at head
      exact ⟨final, state ▸ appendSegment head suffix, terminal⟩
    | replyTimeout invoked same rest =>
      obtain ⟨final, suffix, terminal⟩ := ib rest
      have head := (contracts .reply _ _ _ registered invoked).2
      simp [callBefore, callAfter, same] at head
      exact ⟨final, state ▸ appendSegment head suffix, terminal⟩
  | decode registered _ state =>
    cases run with
    | decode invoked =>
      have head := (contracts .decode _ _ _ registered invoked).2
      simp only [callBefore] at head
      exact ⟨_, state ▸ head, terminals _⟩
  | timeout _ step => cases run; exact ⟨_, singleSegment step, timedOut⟩

/-- Structural source work and modeled participant work are separate quantities.
    Combining them requires a compatible node charge and disjoint accounting. -/
theorem connectedCostBound {s registry timeout core ctx program}
    (connected : Connect s registry timeout core ctx program) {external env value calls work trace}
    (run : Evaluates external core env value calls work)
    (modeled : Executes s external program env value calls work trace)
    (contracts : Contracts s registry external)
    (terminals : ∀ value, callAfter .decode value ∈ (RpcProtocol.contract s).terminal)
    (timedOut : "timed_out" ∈ (RpcProtocol.contract s).terminal)
    (state : RpcMailbox.State) (cap rate : RpcCost.Op → Nat) (ledger : RpcCost.Work)
    (fits : RpcCost.Fits state cap) (covered : RpcCost.Covered state rate ledger)
    (association : state.events = trace.map (fun e => e.protocol.name)) (nodeCharge : Nat) :
    (∃ final, Segment s ctx.state trace final ∧ final ∈ (RpcProtocol.contract s).terminal) ∧
    work * nodeCharge + RpcCost.actual .client ledger ≤
      core.budget * nodeCharge + RpcCost.budget .client cap rate ∧
    RpcCost.actual .server ledger ≤ RpcCost.budget .server cap rate := by
  have _names := association
  exact ⟨modelSafe connected modeled contracts terminals timedOut,
    Nat.add_le_add (Nat.mul_le_mul_right _ (localBound run)) (RpcCost.participantSafety _ _ _ _ fits covered .client),
    RpcCost.participantSafety _ _ _ _ fits covered .server⟩

end ReductionBounds.RpcSource
