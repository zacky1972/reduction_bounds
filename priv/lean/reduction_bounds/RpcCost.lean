namespace ReductionBounds.RpcCost

/-- Disjoint modeled work. Coarse receive/inspect observations add no second charge. -/
inductive Op where
  | prepare | monitor | sendRequest | processReply | decodeError | handleTimeout | handleDown
  | receiveSetup | inspect | pattern | guard
  | receiveRequest | sendReply | handleRequest
  deriving DecidableEq

inductive Participant where
  | client | server
  deriving DecidableEq

def operations : List Op :=
  [.prepare, .monitor, .sendRequest, .processReply, .decodeError, .handleTimeout, .handleDown,
   .receiveSetup, .inspect, .pattern, .guard, .receiveRequest, .sendReply, .handleRequest]

def owner : Op → Participant
  | .receiveRequest | .sendReply | .handleRequest => .server
  | _ => .client

def event : Op → String
  | .prepare => "prepare"
  | .monitor => "monitor_peer"
  | .sendRequest => "send_request"
  | .processReply => "process_reply"
  | .decodeError => "decode_error"
  | .handleTimeout => "handle_timeout"
  | .handleDown => "handle_peer_down"
  | .receiveRequest => "receive_request"
  | .sendReply => "send_reply"
  | .handleRequest => "handle_request"
  | _ => ""

def count (s : RpcMailbox.State) : Op → Nat
  | .receiveSetup => s.counts.receives
  | .inspect => s.counts.inspections
  | .pattern => s.counts.patterns
  | .guard => s.counts.guards
  | op => (s.events.filter (· == event op)).length

theorem operationsComplete (op : Op) : op ∈ operations := by cases op <;> decide

theorem operationsUnique : operations.Nodup := by decide

/-- Server handler invocation limit is a separate, explicit condition. -/
def limits (c : RpcMailbox.Config) (serverCalls : Nat) : Op → Nat
  | .receiveSetup => c.mailbox.limits.receives
  | .inspect => c.mailbox.limits.inspections
  | .pattern => c.mailbox.limits.patterns
  | .guard => c.mailbox.limits.guards
  | .sendRequest => c.limits.clientSends
  | .sendReply => c.limits.serverSends
  | .processReply | .decodeError | .handleTimeout | .handleDown => c.limits.handlers
  | .handleRequest => serverCalls
  | _ => c.limits.events

abbrev Work := Op → List Nat

def sum : List Nat → Nat
  | [] => 0
  | x :: xs => x + sum xs

def total (p : Participant) (f : Op → Nat) : Nat :=
  sum (operations.map (fun op => if owner op = p then f op else 0))

def budget (p : Participant) (cap rate : Op → Nat) : Nat :=
  total p (fun op => cap op * rate op)

def actual (p : Participant) (work : Work) : Nat := total p (fun op => sum (work op))

/-- These are application contracts, not measurements or claims about ERTS. -/
def Covered (s : RpcMailbox.State) (rate : Op → Nat) (work : Work) : Prop :=
  ∀ op, (work op).length = count s op ∧ ∀ n ∈ work op, n ≤ rate op

def Fits (s : RpcMailbox.State) (cap : Op → Nat) : Prop := ∀ op, count s op ≤ cap op

theorem sumBound (xs : List Nat) (rate : Nat) (h : ∀ n ∈ xs, n ≤ rate) :
    sum xs ≤ xs.length * rate := by
  induction xs with
  | nil => simp [sum]
  | cons x xs ih =>
    have head := h x (by simp)
    have tail := ih (fun n hn => h n (by simp [hn]))
    simpa [sum, Nat.add_mul, Nat.add_comm] using Nat.add_le_add head tail

theorem totalMono (p : Participant) (f g : Op → Nat) (h : ∀ op, f op ≤ g op) :
    total p f ≤ total p g := by
  unfold total
  have aux : ∀ ops : List Op,
      sum (ops.map (fun op => if owner op = p then f op else 0)) ≤
      sum (ops.map (fun op => if owner op = p then g op else 0)) := by
    intro ops
    induction ops with
    | nil => exact Nat.le_refl _
    | cons op ops ih =>
      simp only [List.map_cons, sum]
      apply Nat.add_le_add _ ih
      split <;> simp_all
  exact aux operations

/-- Every finite modeled execution (including a pending prefix) satisfying the
    count and local work contracts has separate client and server bounds. -/
theorem participantSafety (s : RpcMailbox.State) (cap rate : Op → Nat) (work : Work)
    (fits : Fits s cap) (covered : Covered s rate work) (p : Participant) :
    actual p work ≤ budget p cap rate := by
  apply totalMono
  intro op
  have h := sumBound (work op) (rate op) (covered op).2
  rw [(covered op).1] at h
  exact Nat.le_trans h (Nat.mul_le_mul_right _ (fits op))

/-- A prefix of each operation's work ledger is safe under the same budget.
    The ledger-to-execution correspondence remains an explicit contract. -/
theorem prefixSafety (s : RpcMailbox.State) (cap rate : Op → Nat) (front suffix : Work)
    (fits : Fits s cap) (covered : Covered s rate (fun op => front op ++ suffix op))
    (p : Participant) : actual p front ≤ budget p cap rate := by
  apply Nat.le_trans _ (participantSafety s cap rate _ fits covered p)
  apply totalMono
  intro op
  have aux : ∀ xs ys : List Nat, sum xs ≤ sum (xs ++ ys) := by
    intro xs ys
    induction xs with
    | nil => exact Nat.zero_le _
    | cons x xs ih => simpa [sum] using Nat.add_le_add_left ih x
  exact aux _ _

/-- A handler bound never replaces the receiving/sending frame contract. -/
theorem composeServer (frame handler frameBound handlerBound : Nat)
    (hf : frame ≤ frameBound) (hh : handler ≤ handlerBound) :
    frame + handler ≤ frameBound + handlerBound := Nat.add_le_add hf hh

theorem composeServerCalls (frame handler invocations frameBound handlerBound cap : Nat)
    (hf : frame ≤ frameBound) (hh : handler ≤ handlerBound) (hi : invocations ≤ cap) :
    frame + invocations * handler ≤ frameBound + cap * handlerBound :=
  Nat.add_le_add hf (Nat.mul_le_mul hi hh)

end ReductionBounds.RpcCost
