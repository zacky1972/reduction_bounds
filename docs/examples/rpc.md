# Initial RPC protocol model

This milestone supplies a single-attempt same-node request/response model, not
analysis of an RPC-using function. The client addresses one server by a direct
PID and has at most one outstanding request. Abstract natural-number tokens
identify the request and, optionally, a process monitor. They are not actual
Erlang references, and do not establish freshness or compiler receive optimization.

## Construct a trace

```elixir
alias ReductionBounds.RpcProtocol

{:ok, model} = RpcProtocol.new(7)
names = [:prepare, :send_request, :request_arrived, :receive_request,
         :handle_request, :send_reply, :reply_arrived, :receive_reply, :process_reply]
events = Enum.map(names, fn name ->
  {:ok, event} = RpcProtocol.event(model, name)
  event
end)
{:ok, result} = RpcProtocol.check_trace(model, events)
result.outcome
#=> :success
result.lean_status
#=> :not_checked
```

`prepare` constructs the modeled request; sending does not establish its arrival.
The server receives and handles the request, then sends its reply. Arrival and
unrelated-message observations have no work owner. Client and server work events
have different symbolic units; no numeric cost or combined budget is computed.
The checks validate correlation annotations as well as transition order and
ownership. Structs constructed directly are revalidated, including the canonical
contract, before generating evidence.

`RpcProtocol.event(model, :receive_reply, request_id: 8)` rejects a mismatched
request token. Changing a constructed event's request/monitor token is rejected
again by `check_trace/2`. Request and monitor identifiers are independent fields.

## Outcomes and unfinished prefixes

| Path | Reported outcome |
| --- | --- |
| Empty trace, preparation or waiting prefix | `:pending` |
| Matching reply followed by processing | `:success` |
| `timeout_elapsed`, then `handle_timeout` while awaiting a response | `:timeout` |
| `peer_down`, then `handle_peer_down` after explicit monitor setup | `:peer_terminated` |
| Reply retrieval followed by `decode_error` | `:decode_error` |

For peer termination, construct `RpcProtocol.new(7, monitor_id: 9)` and begin
with `:monitor_peer`. Without this option, monitor/down events are not registered.
The option declares an abstract observation mechanism; it does not prove an actual
monitor was installed on a process. Sending to a peer never implies detection of
its termination. Monitor observations must carry the monitor token, not the
request token.

Timeout observations are allowed in the declared waiting states, before a matching
reply has been observed. Unrelated arrival/inspection observations can interleave
with waiting. This is a coarse supplied protocol: it does not yet define queue
contents, search cursors, first-match selection, guard evaluation or signal races.
The inspection event does not certify that a real message was unmatched.

Every finite prefix is accepted only if its events and states are admissible.
The model does not promise that a nonterminal trace advances. Terminal traces
cannot advance or send a second request. Their boundary is the client's return;
this does not cancel server execution, retract a message, prove queue cleanup or
exclude late replies. Post-return mailbox effects belong to the next mailbox
milestone, not a hidden assumption that late responses disappear.

## Check the supplied model in Lean

The foundation has a low-level proof builder; the top-level RPC analysis API is
deferred until costs and source correspondence are implemented. Using the events
above, the existing verification boundary checks the generated certificate:

```elixir
alias ReductionBounds.{ProofInput, RpcProtocolProof, Verification}

{:ok, candidate, proof} = RpcProtocolProof.build(model, events)
{:ok, postludes} = ProofInput.rpc_postludes(proof)
reports = Verification.verify!(Lynx.Translation.new(postludes: postludes))
Enum.all?(reports, &(&1.status == :ok))
#=> true
candidate.lean_status
#=> :not_checked
```

Building a candidate is not proof evidence and does not promote its status.
Only the successful reports for the exact generated input establish the Lean
claims. They cover canonical transition agreement, the supplied trace, event
ownership, request/monitor correlation and the reported outcome classification.
An observed terminal outcome is not a theorem that all interactions terminate.

The shared RPC theory imports the existing generic protocol theory. Named and
embedded paths use the same packaged source, dependency-aware cache keys and
axiom audits. Checked shared artifacts can be reused across request identifiers;
changing dependencies invalidates dependent artifacts.

## Explicit exclusions

No mailbox semantics, message-size bounds, inspection/retry bounds, client/server
cost bounds, server-bound reuse, progress, source correspondence, concrete ERTS
charges or elapsed-time guarantees are claimed here. Retries, multiplexed requests,
distributed peers, aliases and priority-message semantics are unsupported. Unknown
events/options and altered contracts are errors, not successful model fallbacks.

Run the foundation checks with:

```sh
REDUCTION_BOUNDS_LEAN_JOBS=4 LEAN_NUM_THREADS=2 \
  mix test test/reduction_bounds/rpc_protocol_test.exs \
           test/reduction_bounds/rpc_protocol_proof_test.exs
```

The [proof reference](../proof.md#initial-rpc-model) describes the certificates.
