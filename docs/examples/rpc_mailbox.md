# RPC mailbox, matching and conditions

This milestone adds executable ordinary-message mailbox semantics and explicit
finite size/count conditions to the initial RPC model. It does not yet derive
client/server cost formulas, prove progress or connect actual Core receive code.

## Message data and conditions

`RpcTerm` is a reified grammar: atoms as strings, mathematical integers, binaries,
abstract reference/PID identifiers, cons cells, nil and tuples of arity 2, 3 or 5.
It includes the standard five-field process-monitor notification shape. Maps,
floats, functions and other tuple sizes are currently unsupported. `from_term/1`
reifies the supported actual data but rejects actual references and PIDs; symbolic
identities must be supplied explicitly and their runtime association is unverified.

Three independent dimensions measure each whole message: tree nodes, total binary
bytes and maximum magnitude bit length of embedded integers. Atoms and identities
are opaque symbols; their labels are not an encoded byte size. Zero has zero
magnitude bits; negative `-2^200` needs 201. These are mathematical measures, not
ERTS word counts, copy costs, binary sharing rules or an encoding contract. Port
`ProtocolSize` iodata measures are unchanged.

```elixir
alias ReductionBounds.{Mailbox, RpcConditions, RpcProtocol, RpcTerm}

cap = %RpcTerm.Size{nodes: 100, bytes: 32, integer_bits: 256}
limits = %{steps: 20, arrivals: 4, receives: 1, inspections: 4,
           pattern_attempts: 8, guard_attempts: 4}
protocol_limits = %{events: 30, client_sends: 1, server_sends: 1,
                    response_handlers: 1, retries: 0}
{:ok, session} = RpcProtocol.new(7)
request = {:tuple3, {:atom, "request"}, {:ref, 7}, {:integer, 5}}
reply = {:tuple3, {:atom, "reply"}, {:ref, 7}, {:integer, 9}}
{:ok, profile} = RpcConditions.new(session, request,
  request_size: cap, response_size: cap, message_size: cap,
  limits: limits, protocol_limits: protocol_limits,
  timeout: 0, reply_guard: {:integer_ge, [2], 0})
```

Request, selected response and mailbox-message caps are independent. The mailbox
cap applies to every initial and arriving message, including unrelated messages.
The response cap applies to the whole selected reply or DOWN message. It is not
inferred from the request. Unknown/missing dimensions and missing counters are
errors, not zero or infinity. All count limits are explicit finite naturals.

The finite matching program is retained in the result. A pattern is `:any`, `:pid`,
`{:literal, term}` or a recursive tuple/cons pattern. Supported guards are booleans,
`{:is_integer, path}` and `{:integer_le | :integer_ge, path, integer}`. Paths use
zero-based fields or cons head/tail. Arbitrary callbacks and other guards are
rejected. Patterns and guards are part of the declared model, not extracted code.

## Execute a connected timeline

```elixir
timeline = [
  {:protocol, :prepare}, {:protocol, :send_request}, :begin_receive,
  {:protocol, :request_arrived}, {:protocol, :receive_request},
  {:protocol, :handle_request}, {:protocol, :send_reply},
  {:arrive, reply}, :inspect, :inspect, {:protocol, :process_reply}
]
{:ok, result} = RpcConditions.check_trace(profile, [{:atom, "old"}], timeline)
result.outcome
#=> :success
result.mailbox.queue
#=> [{:atom, "old"}]
result.counts.inspections
#=> 2
result.lean_status
#=> :not_checked
```

The first inspection retains the old unmatched message; the next selects the
reply. The selected message alone is removed, preserving the order of all other
messages. Matching tests clauses in order and evaluates a guard only after its
pattern succeeds. A failed guard continues to the next clause for that same
message, then to the next message if no clause succeeds.

The client clause is correlated with the session's request token. With a monitor,
there is also a `{'DOWN', monitor, 'process', pid, reason}` clause. Raw receive,
reply-arrival, peer-down and timeout observations cannot be inserted as protocol
annotations to bypass mailbox checks. Selection generates the corresponding
coarse RPC observations. Its arrival observation is delayed until selection;
modeled physical arrivals remain separate mailbox actions. Server preparation and
sending still use the initial protocol's explicit environment/work declarations.
Server mailbox execution and the provenance of a received reply remain obligations.

## Cursor, timeout and late responses

A receive begins at the queue head. An unsuccessful inspection retains its message
and advances the cursor. New arrivals append to the queue. A suspended receive
resumes at the cursor without rescanning its rejected prefix. There is no fresh
reference optimization: each new receive restarts from the oldest retained message.

A finite timeout observation, including `after 0`, requires the current search to
be exhausted with no eligible message. An unread message prevents timeout; a
matching selection prevents the timeout branch. `timeout: :infinity` admits no
timeout observation. No clock is measured and no elapsed-time bound follows.

After timeout and client return, a late arrival remains queued and does not revive
the RPC. It can be inspected by a later independent receive. Reusing a correlation
identifier does not prove freshness or make a late response disappear.

The generic `Mailbox.run/3` API supports repeated receives in a supplied action
sequence. Their inspections accumulate across the whole sequence, so even one
initial unrelated message can be inspected twice by two receives. An initial
queue-length bound alone therefore cannot replace a total inspection bound.
The connected RPC model still allows one receive and no retries; multiple RPC
attempts and duplicate server execution require a later protocol extension.

| Counter | Scope |
| --- | --- |
| `steps`, `arrivals`, `receives`, `inspections` | Mailbox actions over the entire supplied window, including late arrivals |
| `pattern_attempts` | Attempted clause patterns, including failures, for all inspected messages |
| `guard_attempts` | Evaluated clause guards after pattern success, including true/false guards |
| `events`, `client_sends`, `server_sends` | Projected/coarse RPC events with participant sends separate |
| `response_handlers` | Reply processing, decode failure, peer-down or timeout handling |
| `retries` | Must be zero for the current single-attempt RPC model |

Attempts are not machine instructions or recursive comparison costs. The full
matching program and message size conditions are available for the later cost
contracts. Mailbox and protocol events overlap; do not add these counts as if
they were disjoint cost events. The rejected-prefix side check is proof/model
validation work, not an additional set of inspections charged to the RPC client.

## Lean checks and proof scope

```elixir
alias ReductionBounds.{ProofInput, RpcMailboxProof, Verification}
{:ok, candidate, proof} = RpcMailboxProof.build(profile, [{:atom, "old"}], timeline)
{:ok, postludes} = ProofInput.rpc_mailbox_postludes(proof)
reports = Verification.verify!(Lynx.Translation.new(postludes: postludes))
Enum.all?(reports, &(&1.status == :ok))
#=> true
```

Lean independently replays the matching program and timeline. It checks initial
and arriving data, final queue and selection, exact counters and their limits,
canonical RPC clauses, request correlation, selected-response size and the
projection into the initial RPC model. It also checks that the standalone mailbox
actions are exactly the mailbox actions in the connected timeline. Named and
embedded paths share these theories, dependency-aware cache keys and axiom audits.

Building/checking an Elixir candidate does not promote `lean_status`. Successful
reports validate the exact reified model only. Passing one finite trace does not
prove that all actual arrivals or receive attempts stay within the supplied limits.
The declared limits are conditions for subsequent universal cost safety. No source
correspondence, server mailbox theorem, progress, concrete runtime charging, receive
optimization or wall-clock guarantee is established here.

```sh
REDUCTION_BOUNDS_LEAN_JOBS=4 LEAN_NUM_THREADS=2 \
  mix test test/reduction_bounds/mailbox_test.exs \
           test/reduction_bounds/mailbox_proof_test.exs
```
