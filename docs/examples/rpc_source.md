# A restricted RPC source connection

This milestone connects a **helper-contracted client fragment** to the
[single-attempt RPC model](rpc.md). It adds finite normal-execution theorems and
a conditional connection to the [mailbox](rpc_mailbox.md) and
[participant cost](rpc_cost.md) layers. It is not native-receive analysis,
unconditional source termination, or a proof of actual runtime costs.

## Accepted source shape

The target has four arguments, in this order: server PID, correlation reference,
request payload and timeout. The currently accepted control structure is:

```elixir
def request(server, reference, input, timeout) do
  message = {:request, reference, input}
  send(server, message)

  case ReplyHelpers.await_reply(server, reference, timeout) do
    {:reply, data} -> ReplyHelpers.decode(data)
    :timeout -> :timeout
  end
end
```

The reply and timeout clauses may be reordered. Guards must be literal true.
The response helper must return either `{:reply, data}` or `:timeout` under its
contract. Decoding returns a supported reified value; the `:decode_error` sentinel
is classified as modeled decoding failure, with other values classified as
completed reply processing. This classification is part of the explicit decode
contract, not inferred by analyzing the decoder body.

The source must directly construct the three-element request tuple with the
same reference and input variables. It sends exactly once through
`:erlang.send/2`; the reply helper receives the same server and reference.
Timeout is either the fourth argument, a nonnegative integer literal equal to
the model timeout, or the literal `:infinity` when the model also uses infinity.
The timeout arm returns `:timeout`. A fresh reference is not created or proved
fresh by this fragment, and no receive scan optimization is enabled.

The implementation recognizes the pinned compiler's actual Core forms:
`c_let` with a three-element `c_tuple`, a `c_seq` containing static
`:erlang.send/2`, a `c_case` over a static reply call, and a static tail decoding
call or literal timeout return. Variable identities, tuple fields, helper MFAs,
clause order and the compiler-generated case-failure fallback are checked.
The fallback is excluded from the normal fragment under the declared helper
result contract; it is not modeled as a harmless return or free work.

Current cost profiles require a unary integer server contract. The request
payload must therefore satisfy that handler's integer input domain. Server
receipt, matching and reply work still require the independent frame contracts
from the cost layer.

## Explicit rejection boundary

The analyzer returns `{:error, {:rpc_source, target, detail}}` for unsupported
syntax and routing. Syntax diagnostics include a structural Core path, such as
`[:body, :body, :reply]`, and the expression kind or failed connection rule.
It does not silently return a model-only proof labeled as a source bound.

The first fragment rejects native `receive` (including compiler receive loops),
monitored sessions, retries or repeated sends, recursion, dynamic calls,
nontrivial guards, exceptions, arbitrary preparation helpers and other control
structures. Wrong destinations, swapped request fields, stale/wrong reference
arguments, wrong timeout constants and decoding the wrong variable are rejected.
A different arity, missing debug information, missing/ambiguous helper contracts,
callbacks and receive-optimization flags are also rejected. Helper module/name
pairs must be distinct in this initial registry, even if argument counts differ.

The reply helper may itself implement native receive, but its implementation is
**not inspected by this source connection**. Selective matching, guard behavior,
scanning, timeout eligibility, reply provenance and helper totality remain
obligations unless established separately. Using such a helper does not turn the
accepted client into native-receive analysis.

## Input and helper contracts

The source theorem is instantiated for a supplied model profile. Its
`InputsHold` premise identifies the abstract server as a PID, equates the
constructed request to `conditions.request`, and associates the timeout argument
with the model timeout. This is an application precondition, not a proof that
runtime PIDs/references have been mapped to the abstraction correctly.

In particular, the current connection identifies the **supplied reified request**,
not every source input merely having a similar size. Size/cost envelopes may
apply more broadly, but automatically extending this correspondence to arbitrary
abstract input domains is later work. Source extraction, Core reification, term
abstraction and serialization remain trusted boundaries.

The kernel checks conditional request construction and correlation facts, and
checks the actual arguments passed to send and the reply helper after the
request binding. Separate result/trace contracts are then assumed for:

| Operation | Contract boundary |
| --- | --- |
| `:erlang.send/2` | Returns the sent term and emits the modeled send event; it does not establish delivery or server execution |
| Reply helper, arity 3 | Normalized reply/timeout result and a correlated finite protocol segment through the required server/observation phases |
| Decode helper, arity 1 | Processing of the selected data and the declared completion/decoding-failure segment |

These are assumptions about implementations, not facts derived from an Elixir
result map. The contracts concern finite normal invocations; they do not assert
that an invocation returns. A handler's replayed integer proof retains its
callee assumptions and does not prove RPC server identity or scheduling.

## Exact theorem boundary

`suppliedConnection` relates the annotation-free source Core to the constrained
RPC program. `suppliedSourceAgreement` says: **if a finite normal source
execution exists and the input and helper contracts hold**, its modeled trace
is correlated and reaches a canonical RPC terminal state. The theorem retains
the same source result, invocation list and local-work count. It does not assert
that a source execution exists or that a blocked helper eventually returns.
The theory checks an empty invocation relation satisfying the result/trace
contracts while admitting no finite normal source return. This counterexample
shows why those contracts are not totality evidence.

The mailbox/cost connection has additional, explicit proof obligations:

- A checked `RpcMailbox.run` certificate for an initial queue, timeline and state.
- Equality between that state's event names and the source trace's event names.
- `ReplyData`: the helper's normalized reply payload is the selected correlated
  mailbox message, or its timeout result corresponds to a timed-out mailbox.
- A checked canonical protocol projection for the source events ending at the
  same mailbox state. Canonical transition determinism establishes final-state
  agreement; event-name equality alone is not treated as a complete connection.
- The initial queue cap, operation-count caps and the cost layer's covered work
  ledger, with its applicability and correspondence assumptions.

`suppliedSourceMailboxBridge` checks how these certificates compose with the
source protocol theorem. `suppliedSourceBound` combines the local source-work
bound and the separate participant budgets under these premises. The builder
**does not synthesize a runtime mailbox/source association**, prove helper
matching from its implementation, or infer a source trace from one supplied
mailbox example. Those obligations stay visible in the result.

The reported source formula is serialized into Lean and checked against the
kernel-checked structural budget and model client budget.

Local work counts structural nodes of the reified fragment, including tuple
construction, sequencing, dispatch and call overhead. It excludes helper bodies,
blocked time and primitive runtime implementation work. This is an abstract
counter, not ERTS reductions. With a compatible natural `source_node` charge in
`:client_work` and a **disjoint accounting contract**, the client formula is:

```text
source_node_bound * source_node_charge + client_model_bound
```

Model operation envelopes cover the helper/primitive work and must exclude the
same local overhead counted by the source nodes. The source-node charge must
cover the chosen interpretation of those local nodes. Both are explicit
applicability assumptions. The result preserves `upper_bounds` as model budgets
and reports the extended formula separately in `client_source_bound`. The server
budget remains separate; participants' units are not added.

## Build and verify

Start with a cost profile from the [RPC cost guide](rpc_cost.md), whose supplied
request corresponds to the intended source inputs:

```elixir
alias ReductionBounds.{RpcSourceProof, ProofInput, Verification}

{:ok, candidate, proof} = RpcSourceProof.build(
  {Example.Client, :request, 4}, cost_profile,
  calls: %{
    reply: {ReplyHelpers, :await_reply, 3},
    decode: {ReplyHelpers, :decode, 1}
  })
# For dynamically compiled targets, also pass beam_binaries: [...].
{:ok, postludes} = ProofInput.rpc_source_postludes(proof,
  handler: candidate.server_contract.kind)
reports = Verification.verify!(Lynx.Translation.new(postludes: postludes),
                              cache: true, shared_modules: true)
true = reports != [] and Enum.all?(reports, &(&1.status == :ok))
```

The builder loads the new source theory and the existing RPC cost closure,
including replayed integer handler dependencies when needed. It uses the same
verification boundary, dependency-aware cache, axiom audit and global job budget.
No separate source runner or limiter is introduced; Port behavior is unchanged.

Builders retain `lean_status: :not_checked` and
`source_correspondence: :certificate_pending`. Requested theorem names are not
successful reports. The analysis does not execute the target or report an
observed RPC outcome. Even after reports succeed, helper contracts, application
inputs and source/mailbox association remain conditional obligations, not
verified implementations. Unfinished source prefixes, exceptions, helper
totality, source termination, runtime correspondence and elapsed time remain
unverified. [Model conditional completion](rpc_completion.md) is not promoted to
source termination. Public workflow integration and broader source coverage are
subsequent work in Issue #4.
