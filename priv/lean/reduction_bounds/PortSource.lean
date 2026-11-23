namespace ReductionBounds.PortSource

open ReductionBounds.Protocol (Event Contract Runs Allowed)

inductive Value where
  | atom (name : String)
  | integer (value : Int)
  | opaque (id : Nat)
  | pair (tag : String) (data : Value)
  | nil
  | cons (head tail : Value)
  deriving DecidableEq

abbrev Env := String → Value

def bind (env : Env) (name : String) (value : Value) : Env :=
  fun key => if key = name then value else env key

inductive Arg where
  | variable (name : String)
  | literal (value : Value)
  deriving DecidableEq

def Arg.eval (env : Env) : Arg → Value
  | .variable name => env name
  | .literal value => value

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
  events : List Event

abbrev External := String → String → List Value → Value → List Event → Prop

def Invokes (external : External) (call : Call) (env : Env) (inv : Invocation) : Prop :=
  inv.moduleName = call.moduleName ∧ inv.functionName = call.functionName ∧
  inv.args = call.args.map (Arg.eval env) ∧ external inv.moduleName inv.functionName inv.args inv.result inv.events

-- Annotation-free accepted Core blocks. Calls, argument identities, bindings,
-- Boolean clause order and reply-pattern order are retained in the certificate.
inductive Core where
  | ret (value : Arg)
  | letCall (binder : String) (call : Call) (body : Core)
  | boolCase (call : Call) (first : Bool) (a b : Core)
  | replyCase (call : Call) (binder : String) (order : List String) (data closed timeout : Core)
  | tailCall (call : Call)
  deriving DecidableEq

def Core.budget : Core → Nat
  | .ret _ => 1
  | .letCall _ call body => 2 + call.args.length + body.budget
  | .boolCase call _ a b => 4 + call.args.length + a.budget + b.budget
  | .replyCase call _ _ a b c => 9 + call.args.length + a.budget + b.budget + c.budget
  | .tailCall call => 1 + call.args.length

inductive Evaluates (external : External) : Core → Env → Value → List Invocation → Nat → Prop where
  | ret : Evaluates external (.ret value) env (value.eval env) [] 1
  | letCall : Invokes external call env inv → Evaluates external body (bind env binder inv.result) value calls work →
      Evaluates external (.letCall binder call body) env value (inv :: calls) (2 + call.args.length + work)
  | boolFirst : Invokes external call env inv → inv.result = .atom (if first then "true" else "false") →
      Evaluates external a env value calls work →
      Evaluates external (.boolCase call first a b) env value (inv :: calls) (4 + call.args.length + work)
  | boolSecond : Invokes external call env inv → inv.result = .atom (if first then "false" else "true") →
      Evaluates external b env value calls work →
      Evaluates external (.boolCase call first a b) env value (inv :: calls) (4 + call.args.length + work)
  | replyData : Invokes external call env inv → inv.result = .pair "data" payload →
      Evaluates external a (bind env binder payload) value calls work →
      Evaluates external (.replyCase call binder order a b c) env value (inv :: calls) (9 + call.args.length + work)
  | replyClosed : Invokes external call env inv → inv.result = .atom "closed" →
      Evaluates external b env value calls work →
      Evaluates external (.replyCase call binder order a b c) env value (inv :: calls) (9 + call.args.length + work)
  | replyTimeout : Invokes external call env inv → inv.result = .atom "timeout" →
      Evaluates external c env value calls work →
      Evaluates external (.replyCase call binder order a b c) env value (inv :: calls) (9 + call.args.length + work)
  | tailCall : Invokes external call env inv →
      Evaluates external (.tailCall call) env inv.result [inv] (1 + call.args.length)

theorem localBound {external core env value calls work} (run : Evaluates external core env value calls work) :
    work ≤ core.budget := by
  induction run <;> simp_all [Core.budget] <;> omega

inductive Role where | prepare | submit | reply | decode deriving DecidableEq
abbrev Registry := Role → String × String

def RegistryValid (registry : Registry) : Prop :=
  registry .submit = ("erlang", "port_command") ∧
    ([Role.prepare, .submit, .reply, .decode].map registry).Nodup

instance (registry : Registry) : Decidable (RegistryValid registry) := by unfold RegistryValid; infer_instance

def Registered (registry : Registry) (role : Role) (call : Call) : Prop :=
  registry role = (call.moduleName, call.functionName) ∧
  call.args.length = (if role = .submit then 3 else 1)

instance (registry : Registry) (role : Role) (call : Call) : Decidable (Registered registry role call) := by
  unfold Registered; infer_instance

structure Context where
  state : String
  port : String
  request : String
  data : String

inductive Program where
  | ret (arg : Arg) (events : List Event) (final : String)
  | prepare (binder : String) (call : Call) (body : Program)
  | submit (call : Call) (first : Bool) (a b : Program)
  | reply (call : Call) (binder : String) (a b c : Program)
  | decode (call : Call)

def ReturnShape (before : String) (events : List Event) (final : String) : Prop :=
  if before = "rejected" then
    events = [⟨"return_rejection", some "caller", some "symbolic_work"⟩] ∧ final = "failed"
  else events = [] ∧ final = before

instance (before : String) (events : List Event) (final : String) :
    Decidable (ReturnShape before events final) := by unfold ReturnShape; infer_instance

-- Reification records the source call; connection checks its role, exact Port
-- and request variables, nosuspend option, reply binding and all control arms.
inductive Connect (contract : Contract) (registry : Registry) : Core → Context → Program → Prop where
  | ret : ReturnShape ctx.state events final →
      Runs contract ctx.state events final → final ∈ contract.terminal →
      Connect contract registry (.ret value) ctx (.ret value events final)
  | prepare : Registered registry .prepare call → binder ≠ ctx.port →
      ctx.state = "idle" →
      Connect contract registry body {ctx with state := "prepared", request := binder} model →
      Connect contract registry (.letCall binder call body) ctx (.prepare binder call model)
  | submit : Registered registry .submit call → registry .submit = ("erlang", "port_command") →
      call.args = [.variable ctx.port, .variable ctx.request,
        .literal (.cons (.atom "nosuspend") .nil)] → ctx.state = "prepared" →
      Connect contract registry a {ctx with state := if first then "awaiting_response" else "rejected"} ma →
      Connect contract registry b {ctx with state := if first then "rejected" else "awaiting_response"} mb →
      Connect contract registry (.boolCase call first a b) ctx (.submit call first ma mb)
  | reply : Registered registry .reply call → call.args = [.variable ctx.port] →
      ctx.state = "awaiting_response" → order.Perm ["data", "closed", "timeout"] →
      binder ≠ ctx.port → binder ≠ ctx.request →
      Connect contract registry a {ctx with state := "response_received", data := binder} ma →
      Connect contract registry b {ctx with state := "closed"} mb →
      Connect contract registry c {ctx with state := "timed_out"} mc →
      Connect contract registry (.replyCase call binder order a b c) ctx (.reply call binder ma mb mc)
  | decode : Registered registry .decode call → call.args = [.variable ctx.data] →
      ctx.state = "response_received" → "complete" ∈ contract.terminal →
      Connect contract registry (.tailCall call) ctx (.decode call)

inductive Executes (external : External) : Program → Env → Value → List Invocation → Nat → List Event → Prop where
  | ret : Executes external (.ret arg events final) env (arg.eval env) [] 1 events
  | prepare : Invokes external call env inv → Executes external body (bind env binder inv.result) value calls work trace →
      Executes external (.prepare binder call body) env value (inv :: calls) (2 + call.args.length + work) (inv.events ++ trace)
  | submitFirst : Invokes external call env inv → inv.result = .atom (if first then "true" else "false") →
      Executes external a env value calls work trace → Executes external (.submit call first a b) env value
        (inv :: calls) (4 + call.args.length + work) (inv.events ++ trace)
  | submitSecond : Invokes external call env inv → inv.result = .atom (if first then "false" else "true") →
      Executes external b env value calls work trace → Executes external (.submit call first a b) env value
        (inv :: calls) (4 + call.args.length + work) (inv.events ++ trace)
  | replyData : Invokes external call env inv → inv.result = .pair "data" payload →
      Executes external a (bind env binder payload) value calls work trace → Executes external (.reply call binder a b c)
        env value (inv :: calls) (9 + call.args.length + work) (inv.events ++ trace)
  | replyClosed : Invokes external call env inv → inv.result = .atom "closed" →
      Executes external b env value calls work trace → Executes external (.reply call binder a b c)
        env value (inv :: calls) (9 + call.args.length + work) (inv.events ++ trace)
  | replyTimeout : Invokes external call env inv → inv.result = .atom "timeout" →
      Executes external c env value calls work trace → Executes external (.reply call binder a b c)
        env value (inv :: calls) (9 + call.args.length + work) (inv.events ++ trace)
  | decode : Invokes external call env inv →
      Executes external (.decode call) env inv.result [inv] (1 + call.args.length) inv.events

theorem sourceAgreement {contract registry source ctx model} (connected : Connect contract registry source ctx model)
    {external env value calls work} (run : Evaluates external source env value calls work) :
    ∃ trace, Executes external model env value calls work trace := by
  induction connected generalizing env value calls work with
  | ret => cases run; exact ⟨_, .ret⟩
  | prepare _ _ _ _ ih =>
    cases run with
    | letCall invoked rest => obtain ⟨trace, modeled⟩ := ih rest; exact ⟨_, .prepare invoked modeled⟩
  | submit _ _ _ _ _ _ ia ib =>
    cases run with
    | boolFirst invoked same rest => obtain ⟨trace, modeled⟩ := ia rest; exact ⟨_, .submitFirst invoked same modeled⟩
    | boolSecond invoked same rest => obtain ⟨trace, modeled⟩ := ib rest; exact ⟨_, .submitSecond invoked same modeled⟩
  | reply _ _ _ _ _ _ _ _ _ ia ib ic =>
    cases run with
    | replyData invoked same rest => obtain ⟨trace, modeled⟩ := ia rest; exact ⟨_, .replyData invoked same modeled⟩
    | replyClosed invoked same rest => obtain ⟨trace, modeled⟩ := ib rest; exact ⟨_, .replyClosed invoked same modeled⟩
    | replyTimeout invoked same rest => obtain ⟨trace, modeled⟩ := ic rest; exact ⟨_, .replyTimeout invoked same modeled⟩
  | decode => cases run with | tailCall invoked => exact ⟨_, .decode invoked⟩

def callBefore : Role → String
  | .prepare => "idle" | .submit => "prepared" | .reply => "awaiting_response" | .decode => "response_received"

def callAfter : Role → Value → String
  | .prepare, _ => "prepared"
  | .submit, .atom "true" => "awaiting_response"
  | .submit, _ => "rejected"
  | .reply, .pair "data" _ => "response_received"
  | .reply, .atom "closed" => "closed"
  | .reply, _ => "timed_out"
  | .decode, _ => "complete"

theorem submitAfterFirst (first : Bool) :
    callAfter .submit (.atom (if first then "true" else "false")) =
      (if first then "awaiting_response" else "rejected") := by cases first <;> rfl

theorem submitAfterSecond (first : Bool) :
    callAfter .submit (.atom (if first then "false" else "true")) =
      (if first then "rejected" else "awaiting_response") := by cases first <;> rfl

def ResultAllowed : Role → Value → Prop
  | .submit, value => value = .atom "true" ∨ value = .atom "false"
  | .reply, value => (∃ payload, value = .pair "data" payload) ∨ value = .atom "closed" ∨ value = .atom "timeout"
  | _, _ => True

def Contracts (contract : Contract) (registry : Registry) (external : External) : Prop :=
  ∀ role call env inv, Registered registry role call → Invokes external call env inv →
    ResultAllowed role inv.result ∧ Runs contract (callBefore role) inv.events (callAfter role inv.result)

theorem appendRuns {contract before middle final first second}
    (a : Runs contract before first middle) (b : Runs contract middle second final) :
    Runs contract before (first ++ second) final := by
  induction a with
  | nil => exact b
  | cons step _ ih => exact .cons step (ih b)

theorem modelSafe {contract registry source ctx model} (connected : Connect contract registry source ctx model)
    {external env value calls work trace} (run : Executes external model env value calls work trace)
    (contracts : Contracts contract registry external) :
    ∃ final, Runs contract ctx.state trace final ∧ final ∈ contract.terminal := by
  induction connected generalizing env value calls work trace with
  | ret _ allowed terminal => cases run; exact ⟨_, allowed, terminal⟩
  | @prepare call binder ctx body model registered _ state _ ih =>
    cases run with
    | prepare invoked rest =>
      obtain ⟨final, suffix, terminal⟩ := ih rest
      have headRun := (contracts .prepare call _ _ registered invoked).2
      simp only [callBefore, callAfter] at headRun
      exact ⟨final, state ▸ appendRuns headRun suffix, terminal⟩
  | @submit call first ctx a ma b mb registered _ _ state _ _ ia ib =>
    cases run with
    | submitFirst invoked same rest =>
      obtain ⟨final, suffix, terminal⟩ := ia rest
      have headRun := (contracts .submit call _ _ registered invoked).2
      simp only [callBefore, same, submitAfterFirst] at headRun
      exact ⟨final, state ▸ appendRuns headRun suffix, terminal⟩
    | submitSecond invoked same rest =>
      obtain ⟨final, suffix, terminal⟩ := ib rest
      have headRun := (contracts .submit call _ _ registered invoked).2
      simp only [callBefore, same, submitAfterSecond] at headRun
      exact ⟨final, state ▸ appendRuns headRun suffix, terminal⟩
  | @reply call ctx order binder a ma b mb c mc registered _ state _ _ _ _ _ _ ia ib ic =>
    cases run with
    | replyData invoked same rest =>
      obtain ⟨final, suffix, terminal⟩ := ia rest
      have headRun := (contracts .reply call _ _ registered invoked).2
      simp [callBefore, callAfter, same] at headRun
      exact ⟨final, state ▸ appendRuns headRun suffix, terminal⟩
    | replyClosed invoked same rest =>
      obtain ⟨final, suffix, terminal⟩ := ib rest
      have headRun := (contracts .reply call _ _ registered invoked).2
      simp [callBefore, callAfter, same] at headRun
      exact ⟨final, state ▸ appendRuns headRun suffix, terminal⟩
    | replyTimeout invoked same rest =>
      obtain ⟨final, suffix, terminal⟩ := ic rest
      have headRun := (contracts .reply call _ _ registered invoked).2
      simp [callBefore, callAfter, same] at headRun
      exact ⟨final, state ▸ appendRuns headRun suffix, terminal⟩
  | @decode call ctx registered _ state terminal =>
    cases run with
    | decode invoked =>
      have headRun := (contracts .decode call _ _ registered invoked).2
      exact ⟨"complete", state ▸ headRun, terminal⟩

theorem connectedCostBound {contract registry source ctx model}
    (connected : Connect contract registry source ctx model)
    {external env value calls work trace}
    (run : Evaluates external source env value calls work)
    (modeled : Executes external model env value calls work trace)
    (contracts : Contracts contract registry external)
    (spec : ReductionBounds.ProtocolConditions.Spec)
    (entries : List ReductionBounds.ProtocolCost.Entry) (groups : List ReductionBounds.ProtocolCost.Group)
    (charge : ReductionBounds.ProtocolCost.Charges) (states : List String)
    (observations : List ReductionBounds.ProtocolConditions.Observation)
    (good : ReductionBounds.ProtocolCost.CostSpecGood contract spec entries groups)
    (rows : ReductionBounds.ProtocolConditions.RowsHold spec ctx.state trace states observations)
    (counts : ReductionBounds.ProtocolConditions.CountsHold spec ctx.state trace states) :
    (∃ final, Runs contract ctx.state trace final ∧ final ∈ contract.terminal) ∧
    work * charge "caller" "source_node" +
        ReductionBounds.ProtocolCost.traceCost entries charge "caller" ctx.state trace states observations ≤
      source.budget * charge "caller" "source_node" + ReductionBounds.ProtocolCost.ownerBound spec groups charge "caller" := by
  exact ⟨modelSafe connected modeled contracts,
    Nat.add_le_add (Nat.mul_le_mul_right _ (localBound run))
      (ReductionBounds.ProtocolCost.costSafety contract spec entries groups charge "caller" ctx.state trace states observations good rows counts)⟩

end ReductionBounds.PortSource
