# RPC participant cost safety and server contracts

This layer extends the [single-attempt RPC](rpc.md) and
[mailbox conditions](rpc_mailbox.md) with separate client and server budgets.
It proves conditional cost safety, including finite pending prefixes. It does
not prove successful return, timeout completion, source-level RPC behavior,
ERTS reductions, or elapsed time. Retries remain zero.

## Declaring envelopes

Each modeled operation has a nonnegative natural cost envelope. The caller must
supply every rate except `:handle_request`, which comes from the server contract.
A rate has exactly `:upper_bound` and `:cost_unit`. Client rates require
`:client_work`; server rates require `:server_work`. Explicit zero rates are
allowed. Missing rates, unknown operations, mixed units and unknown bounds are
rejected. Client and server budgets are never summed into a combined scalar.

The rates apply under these **assumed applicability contracts**:

- Client work uses the declared request, response and message size caps, fixed
  matching program, initial queue cap, arrival cap and execution count limits.
  Queue length is bounded by `initial_messages + mailbox.limits.arrivals`.
- An inspection rate covers its own structural overhead. Pattern and guard
  attempt rates separately cover their entire modeled matching work, including
  traversal of large messages and integers under the size caps. These are
  envelopes per attempt, not claims that each attempt is one machine instruction.
- Server receive/send work uses an independent frame declaration: message and
  reply size caps, initial queue length, arrivals, inspections, pattern attempts
  and guard attempts. The receive envelope must cover server queue selection;
  it is not borrowed from the checked **client** mailbox counters. The frame
  is assumed, not a server mailbox execution certificate. Outgoing reply size
  remains a server contract even when a reply has not arrived at the client.
- Input payload association, handler identity, reply encoding and runtime
  implementation of these operations remain explicit correspondence obligations.

Rates may be computed externally from size-dependent functions, but this API
accepts the resulting finite envelopes, not callbacks or arbitrary Lean code.
Declaring a rate does not establish that a runtime satisfies it. The current
prototype does not automatically derive optimal rates from the caps.

## Disjoint accounting

| Owner | Work | Count source |
| --- | --- | --- |
| Client | prepare, monitor, send request | Canonical protocol event occurrences |
| Client | process reply, decode error, timeout handler, DOWN handler | Canonical protocol event occurrences |
| Client | receive setup, inspection, pattern attempt, guard attempt | Replayed client mailbox counters |
| Server | receive request, send reply | Canonical protocol event occurrences |
| Server | handler | Canonical protocol occurrences, with explicit invocation cap |
| Environment | arrivals, timeout elapsed, peer down | No participant charge |

`inspect_unrelated` and `receive_reply` are coarse observations of work already
represented by mailbox counters; they do not introduce extra charges. Pattern
and guard work must be excluded from the inspection overhead envelope to avoid
charging the same work twice. Runtime work absent from this model is outside
the theorem, not implicitly free.

The budget for each participant is the sum of `count_cap * rate` over its
operations. General protocol work uses the event limit; sends use send limits,
terminal handlers use the handler limit, and mailbox work uses mailbox limits.
This is conservative: mutually exclusive terminal alternatives can each
contribute to the budget. The server handler invocation cap is separately
required and is currently at most one. An observed trace with fewer operations
does not establish a smaller bound for every future execution.

## Assumed versus replayed server handlers

The first supported server contract is a unary integer handler. Its payload is
read from the supplied `{:request, request_ref, integer}` model term (using the
reified grammar in the mailbox guide). Its declared integer input domain must
contain that payload.

An assumed handler contract explicitly leaves its numeric cost bound unproved:

```elixir
alias ReductionBounds.{IntegerSize, RpcServerContract, RpcTerm}

size = %RpcTerm.Size{nodes: 100, bytes: 32, integer_bits: 256}
frame = %{
  message_size: size, reply_size: size,
  initial_messages: 10, arrivals: 10, inspections: 20,
  pattern_attempts: 20, guard_attempts: 20
}
input = %IntegerSize{lower: 0, upper: 10, magnitude_bits: 4}
{:ok, server} = RpcServerContract.assume({Example.Server, :handle, 1}, input, 30, frame)
```

Alternatively, reuse an integer-cost candidate with a **declarative** cost
contract in `:server_work`. The proof builder recovers its current Core,
reconstructs the integer derivation and checked callees, compares all evidence
and instantiates the same cost contract through the existing bound-transfer
proof. It does not trust a saved `:checked` status or numeric bound. Nested
external callee contracts remain assumptions. No reduction-to-time conversion
or communication transfer theorem is inferred.

```elixir
alias ReductionBounds.{CostContract, RpcServerContract}

functions = Map.new(CostContract.operations(), &{&1, {:add, 1, {:max, :left, :right}}})
{:ok, charges} = CostContract.new(id: :server_model, cost_unit: :server_work,
                                 functions: functions)
{:ok, original} = ReductionBounds.infer_integer_cost_bound(
  {Example.Server, :handle, 1}, input_sizes: [input], cost_contract: charges)
{:ok, server} = RpcServerContract.reuse(original, frame)
# For dynamically compiled handlers, pass beam_binaries: [...] to reuse/3.
```

Only unary integer payloads are supported here. Symbolic operation functions,
incompatible units, altered Core evidence and uncovered inputs are rejected.
Supporting other handler fragments or request encodings is later work.

## Building and checking a proof

With `conditions`, `initial_queue` and `timeline` from the mailbox guide:

```elixir
alias ReductionBounds.{RpcCost, RpcCostProof, ProofInput, Verification}

# Illustrative model envelopes only; these are not measured VM costs.
rates = Map.new(RpcCost.operations() -- [:handle_request], fn operation ->
  unit = if RpcCost.owner(operation) == :client, do: :client_work, else: :server_work
  {operation, %{cost_unit: unit, upper_bound: 2}}
end)
{:ok, profile} = RpcCost.new(conditions, rates, server,
                           initial_messages: 10, server_calls: 1)
{:ok, candidate, proof} = RpcCostProof.build(profile, initial_queue, timeline)
{:ok, postludes} = ProofInput.rpc_cost_postludes(proof,
  handler: candidate.server_contract.kind)
reports = Verification.verify!(Lynx.Translation.new(postludes: postludes),
                              cache: true, shared_modules: true)
true = reports != [] and Enum.all?(reports, &(&1.status == :ok))
```

This is a low-level workflow through the existing verification boundary, job
budget, cache and axiom audit. Builders always retain `lean_status: :not_checked`;
`checked_theorems` lists requested obligations and is not verification evidence.
A reused handler has `status: :replay_pending` until reports are checked; an
assumed handler stays `:assumed` even when all proof reports succeed. No public
RPC source-analysis API or automatic status promotion is introduced here.

## Exact theorem boundary

The shared Lean theory fixes a finite operation registry, owners and the
extraction of operation counts from a replayed mailbox/protocol state. A work
ledger assigns a list of natural costs to each operation. Coverage means its
list length equals that operation's semantic count and each cost satisfies its
declared envelope. Mapping all actual runtime work to that ledger is an explicit
application contract, not a proved property of a BEAM process.

`participantSafety` proves a bound for **any** state whose extracted counts fit
the caps and whose ledger is covered. `prefixSafety` proves the same bound for
each operation's ledger prefix. The generated `admittedCostSafety` specializes
this to any supplied-model RPC execution, under explicit count and work
contracts; it does not infer future count bounds from the example trace.
`suppliedCountsMatch` and `suppliedCountsFit` independently check the concrete
witness. Numeric client/server budget identities are checked by the kernel.

For replayed handlers, `RpcHandler.replayedCostSafety` and
`RpcHandler.replayedPrefixSafety` discharge the handler
cost envelope from the integer execution theorem for **every** handler entry in
the ledger, retaining only the other operation envelopes and explicit callee
contracts. `RpcHandler.requestArgumentMatches` connects the checked request to the
handler environment, and `RpcHandler.requestInputCovered` checks payload-domain
membership in Lean. `RpcHandler.composedServerBound` combines a modeled handler run with the
separate receive/send frame and invocation limit to reach the declared server
budget. For assumed handlers, the analogous composition theorem retains the
handler inequality as a premise.

These model costs treat the handler event atomically. Cost of arbitrary
unfinished server source executions, late server work after client return,
source-level exception paths and actual server mailbox scanning are not proved.
Cost safety does not establish arrival, fairness, scheduling, successful reply,
or deadline completion. The [conditional completion layer](rpc_completion.md) adds explicit progress
premises independently of these cost theorems.
