namespace ReductionBounds.RpcProtocol

open ReductionBounds.Protocol

-- These two fixed declarations are checked against the Elixir model in every
-- generated certificate; supplied transitions are not accepted as RPC semantics.
def unmonitoredContract : Contract := {
  participants := [("client", "client_work"), ("server", "server_work")]
  states := ["idle", "monitored", "prepared", "awaiting_request", "request_available", "request_received", "reply_ready", "awaiting_reply", "reply_available", "reply_received", "timeout_observed", "peer_down_observed", "complete", "timed_out", "peer_terminated", "decode_failed"]
  initial := "idle"
  terminal := ["complete", "timed_out", "peer_terminated", "decode_failed"]
  events := [⟨"decode_error", (some "client"), (some "client_work")⟩, ⟨"handle_request", (some "server"), (some "server_work")⟩, ⟨"handle_timeout", (some "client"), (some "client_work")⟩, ⟨"inspect_unrelated", (some "client"), (some "client_work")⟩, ⟨"prepare", (some "client"), (some "client_work")⟩, ⟨"process_reply", (some "client"), (some "client_work")⟩, ⟨"receive_reply", (some "client"), (some "client_work")⟩, ⟨"receive_request", (some "server"), (some "server_work")⟩, ⟨"reply_arrived", none, none⟩, ⟨"request_arrived", none, none⟩, ⟨"send_reply", (some "server"), (some "server_work")⟩, ⟨"send_request", (some "client"), (some "client_work")⟩, ⟨"timeout_elapsed", none, none⟩, ⟨"unrelated_arrived", none, none⟩]
  transitions := [⟨"idle", "prepare", "prepared"⟩, ⟨"prepared", "send_request", "awaiting_request"⟩, ⟨"awaiting_request", "request_arrived", "request_available"⟩, ⟨"request_available", "receive_request", "request_received"⟩, ⟨"request_received", "handle_request", "reply_ready"⟩, ⟨"reply_ready", "send_reply", "awaiting_reply"⟩, ⟨"awaiting_reply", "reply_arrived", "reply_available"⟩, ⟨"reply_available", "receive_reply", "reply_received"⟩, ⟨"reply_received", "process_reply", "complete"⟩, ⟨"reply_received", "decode_error", "decode_failed"⟩, ⟨"timeout_observed", "handle_timeout", "timed_out"⟩, ⟨"awaiting_request", "unrelated_arrived", "awaiting_request"⟩, ⟨"awaiting_request", "inspect_unrelated", "awaiting_request"⟩, ⟨"request_available", "unrelated_arrived", "request_available"⟩, ⟨"request_available", "inspect_unrelated", "request_available"⟩, ⟨"request_received", "unrelated_arrived", "request_received"⟩, ⟨"request_received", "inspect_unrelated", "request_received"⟩, ⟨"reply_ready", "unrelated_arrived", "reply_ready"⟩, ⟨"reply_ready", "inspect_unrelated", "reply_ready"⟩, ⟨"awaiting_reply", "unrelated_arrived", "awaiting_reply"⟩, ⟨"awaiting_reply", "inspect_unrelated", "awaiting_reply"⟩, ⟨"reply_available", "unrelated_arrived", "reply_available"⟩, ⟨"reply_available", "inspect_unrelated", "reply_available"⟩, ⟨"awaiting_request", "timeout_elapsed", "timeout_observed"⟩, ⟨"request_available", "timeout_elapsed", "timeout_observed"⟩, ⟨"request_received", "timeout_elapsed", "timeout_observed"⟩, ⟨"reply_ready", "timeout_elapsed", "timeout_observed"⟩, ⟨"awaiting_reply", "timeout_elapsed", "timeout_observed"⟩]
}

def monitoredContract : Contract := {
  participants := [("client", "client_work"), ("server", "server_work")]
  states := ["idle", "monitored", "prepared", "awaiting_request", "request_available", "request_received", "reply_ready", "awaiting_reply", "reply_available", "reply_received", "timeout_observed", "peer_down_observed", "complete", "timed_out", "peer_terminated", "decode_failed"]
  initial := "idle"
  terminal := ["complete", "timed_out", "peer_terminated", "decode_failed"]
  events := [⟨"decode_error", (some "client"), (some "client_work")⟩, ⟨"handle_peer_down", (some "client"), (some "client_work")⟩, ⟨"handle_request", (some "server"), (some "server_work")⟩, ⟨"handle_timeout", (some "client"), (some "client_work")⟩, ⟨"inspect_unrelated", (some "client"), (some "client_work")⟩, ⟨"monitor_peer", (some "client"), (some "client_work")⟩, ⟨"peer_down", none, none⟩, ⟨"prepare", (some "client"), (some "client_work")⟩, ⟨"process_reply", (some "client"), (some "client_work")⟩, ⟨"receive_reply", (some "client"), (some "client_work")⟩, ⟨"receive_request", (some "server"), (some "server_work")⟩, ⟨"reply_arrived", none, none⟩, ⟨"request_arrived", none, none⟩, ⟨"send_reply", (some "server"), (some "server_work")⟩, ⟨"send_request", (some "client"), (some "client_work")⟩, ⟨"timeout_elapsed", none, none⟩, ⟨"unrelated_arrived", none, none⟩]
  transitions := [⟨"idle", "monitor_peer", "monitored"⟩, ⟨"monitored", "prepare", "prepared"⟩, ⟨"prepared", "send_request", "awaiting_request"⟩, ⟨"awaiting_request", "request_arrived", "request_available"⟩, ⟨"request_available", "receive_request", "request_received"⟩, ⟨"request_received", "handle_request", "reply_ready"⟩, ⟨"reply_ready", "send_reply", "awaiting_reply"⟩, ⟨"awaiting_reply", "reply_arrived", "reply_available"⟩, ⟨"reply_available", "receive_reply", "reply_received"⟩, ⟨"reply_received", "process_reply", "complete"⟩, ⟨"reply_received", "decode_error", "decode_failed"⟩, ⟨"timeout_observed", "handle_timeout", "timed_out"⟩, ⟨"awaiting_request", "unrelated_arrived", "awaiting_request"⟩, ⟨"awaiting_request", "inspect_unrelated", "awaiting_request"⟩, ⟨"request_available", "unrelated_arrived", "request_available"⟩, ⟨"request_available", "inspect_unrelated", "request_available"⟩, ⟨"request_received", "unrelated_arrived", "request_received"⟩, ⟨"request_received", "inspect_unrelated", "request_received"⟩, ⟨"reply_ready", "unrelated_arrived", "reply_ready"⟩, ⟨"reply_ready", "inspect_unrelated", "reply_ready"⟩, ⟨"awaiting_reply", "unrelated_arrived", "awaiting_reply"⟩, ⟨"awaiting_reply", "inspect_unrelated", "awaiting_reply"⟩, ⟨"reply_available", "unrelated_arrived", "reply_available"⟩, ⟨"reply_available", "inspect_unrelated", "reply_available"⟩, ⟨"awaiting_request", "timeout_elapsed", "timeout_observed"⟩, ⟨"request_available", "timeout_elapsed", "timeout_observed"⟩, ⟨"request_received", "timeout_elapsed", "timeout_observed"⟩, ⟨"reply_ready", "timeout_elapsed", "timeout_observed"⟩, ⟨"awaiting_reply", "timeout_elapsed", "timeout_observed"⟩, ⟨"peer_down_observed", "handle_peer_down", "peer_terminated"⟩, ⟨"awaiting_request", "peer_down", "peer_down_observed"⟩, ⟨"request_available", "peer_down", "peer_down_observed"⟩, ⟨"request_received", "peer_down", "peer_down_observed"⟩, ⟨"reply_ready", "peer_down", "peer_down_observed"⟩, ⟨"awaiting_reply", "peer_down", "peer_down_observed"⟩]
}

structure Session where
  requestId : Nat
  monitorId : Option Nat

structure Event where
  protocol : Protocol.Event
  requestId : Option Nat
  monitorId : Option Nat
  deriving DecidableEq

def contract (session : Session) : Protocol.Contract :=
  if session.monitorId.isSome then monitoredContract else unmonitoredContract

def requestEvents : List String :=
  ["prepare", "send_request", "request_arrived", "receive_request", "handle_request",
   "send_reply", "reply_arrived", "receive_reply", "process_reply", "decode_error"]

def monitorEvents : List String := ["monitor_peer", "peer_down", "handle_peer_down"]

def Correlated (session : Session) (event : Event) : Prop :=
  event.requestId = (if requestEvents.contains event.protocol.name then some session.requestId else none) ∧
  event.monitorId = (if monitorEvents.contains event.protocol.name then session.monitorId else none) ∧
  (monitorEvents.contains event.protocol.name = true → session.monitorId ≠ none)

instance (session : Session) (event : Event) : Decidable (Correlated session event) :=
  inferInstanceAs (Decidable (_ ∧ _ ∧ _))

def ValidTrace (session : Session) (events : List Event) (final : String) : Prop :=
  Protocol.Runs (contract session) (contract session).initial (events.map Event.protocol) final ∧
  ∀ event ∈ events, Correlated session event

def checkTrace (session : Session) (events : List Event) (states : List String) : Bool :=
  Protocol.checkTrace (contract session) (events.map Event.protocol) states &&
    events.all (fun event => decide (Correlated session event))

theorem checkTraceSound (session : Session) (events : List Event) (states : List String)
    (accepted : checkTrace session events states = true) :
    (contract session).wellFormed = true ∧
      ValidTrace session events (Protocol.finish (contract session).initial states) := by
  have parts := Bool.and_eq_true_iff.mp accepted
  have protocol := Protocol.checkTraceSound _ _ _ parts.1
  refine ⟨protocol.1, protocol.2, ?_⟩
  intro event member
  exact of_decide_eq_true (List.all_eq_true.mp parts.2 event member)

theorem ValidTrace.requestCorrelation {session : Session} {events : List Event} {final : String}
    (trace : ValidTrace session events final) (event : Event) (member : event ∈ events)
    (request : requestEvents.contains event.protocol.name = true) :
    event.requestId = some session.requestId := by
  have correlation := (trace.2 event member).1
  rw [request] at correlation
  exact correlation

theorem ValidTrace.monitorCorrelation {session : Session} {events : List Event} {final : String}
    (trace : ValidTrace session events final) (event : Event) (member : event ∈ events)
    (monitor : monitorEvents.contains event.protocol.name = true) :
    event.monitorId = session.monitorId ∧ session.monitorId ≠ none := by
  have correlation := trace.2 event member
  have same := correlation.2.1
  rw [monitor] at same
  exact ⟨same, correlation.2.2 monitor⟩

def outcome : String → String
  | "complete" => "success"
  | "timed_out" => "timeout"
  | "peer_terminated" => "peer_terminated"
  | "decode_failed" => "decode_error"
  | _ => "pending"

end ReductionBounds.RpcProtocol
