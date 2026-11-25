<!-- cspell:words mathrm operatorname -->
# Conditional RPC completion

Completion is a separate claim from [participant cost safety](rpc_cost.md).
Finite work budgets do not establish that a suspended client resumes, a server
runs, or a message arrives. This layer proves conditional model completion under
explicit progress premises, using the [checked RPC/mailbox model](rpc_mailbox.md).
It does not establish source termination, scheduling guarantees, or wall-clock
deadlines. The scope remains an ordinary same-node, single-attempt interaction;
retries remain zero.

## Claims and assumptions

| Claim | Additional assumptions |
| --- | --- |
| Conditional cost safety for finite executions/prefixes | Size/count contracts, local cost envelopes and work-ledger correspondence; no progress premise |
| Eventual modeled termination | Client, request, server and response progress, respecting all remaining limits |
| Eventual successful modeled reply handling | The same progress premises plus exclusion of timeout, peer death and decoding failure |
| Source termination or an elapsed time bound | Not established by this layer |

`RpcCompletion.check_trace/4` assesses an existing mailbox conditions profile,
initial queue and timeline. Its options are `progress: [...]` and
`goal: :termination | :success`, defaulting to `:termination`.

The four progress declarations quantify over **every admitted continuation**,
not only the supplied finite example:

| Declaration | Control states | Meaning |
| --- | --- | --- |
| `:client_progress` | idle, monitored, prepared, reply received, timeout observed, DOWN observed | An admitted next action eventually occurs, including client setup or terminal handling |
| `:request_progress` | awaiting request | An admitted next action eventually occurs while waiting for request delivery or an alternative outcome |
| `:server_progress` | request available, request received, reply ready | An admitted next action eventually occurs through server receipt, handling and reply submission |
| `:response_progress` | awaiting reply, reply available | An admitted next action eventually occurs through delivery, client resumption and mailbox processing |

An eventual action may be another permitted arrival or inspection. Since every
mailbox action consumes a bounded allowance, and every other admitted protocol
action decreases the control phase, progress cannot perpetually consist of
unrelated active work. A declaration includes compatibility with the remaining
size/count limits; it does not prove that the real environment satisfies them.
It is not a claim that a particular reply must arrive as the next action.

`goal: :success` additionally requires `:no_failure_outcomes`. In Lean this
excludes entering timeout-observed, DOWN-observed, timed-out, peer-terminated and
decoding-failed states on every active transition. It is a universal application
premise, not an inference from the absence of failures in an example.
Termination permits success, timeout handling, monitored peer termination or
decoding failure. It does not imply that a timeout cancels server computation or
retracts a late reply.

An integer handler cost bound, even when replayed successfully, supplies none of
these progress premises. It does not prove server scheduling, message delivery,
client resumption, source-level totality of the whole RPC, or deadlines.

## The active-work argument

The completion model instruments the existing mailbox state with a remaining
mailbox-action allowance. It starts at `conditions.mailbox.limits.steps` and
maintains:

```math
R+j=L,\qquad \rho=12R+p.
```

Here `$R$` is `remaining`, `$j$` is `model.counts.steps`,
`$L$` is `conditions.mailbox.limits.steps`, and
`$p=\operatorname{phase}(\mathrm{model.protocolState})$`.

Canonical RPC phases range from 11 at initial setup to zero at terminal states.
Every active action decreases this natural rank:

- An arrival, receive setup, inspection or timeout consumes one mailbox step.
  The total step limit covers the whole interaction, not just the initial queue.
- An explicit protocol action follows a checked canonical RPC edge whose phase
  decreases. No extra retry or polling transition is introduced.
- A suspended interval is represented by `none`. Its configuration remains
  unchanged, and it consumes no active-action allowance.

Every instrumented step checks the original mailbox transition, both families
of count caps, counter balance, the known control state and the applicable
control-edge certificate. `Moves.erased` maps it back to the original
`RpcMailbox.Runs` relation. Selection, guards, timeout eligibility, correlation
and unmatched-message retention still use the existing checked semantics.
The completion model does not accept arbitrary receive or timeout annotations.

The rank yields an upper bound of `$11+12L$` on active
**timeline items**. A mailbox inspection can project multiple coarse protocol
events; the action bound counts the timeline item once. It is a conservative
proof rank, not an additional cost formula, an optimal operation count or a
unit of time. Receive, inspection, arrival and retry conditions continue to be
enforced by the original model.

The shared theorem uses strong induction on the rank together with eventual
progress at every nonterminal point of an infinite behavior. Arbitrarily long
finite suspension is allowed. Without progress, an infinitely suspended valid
behavior is possible. `stalledNotComplete` and `stalledNoProgress` check that
counterexample explicitly, including profiles with a finite timeout value.
A timeout numeral alone does not force a modeled timeout action to occur.

## Assessing a supplied trace

Using `conditions`, `initial_queue` and `timeline` from the mailbox guide:

```elixir
alias ReductionBounds.RpcCompletion

progress = [:client_progress, :request_progress,
            :server_progress, :response_progress]
{:ok, result} = RpcCompletion.check_trace(conditions, initial_queue, timeline,
  goal: :success, progress: progress ++ [:no_failure_outcomes])
result.completion.status
# :conditional when declared assumptions and observed conditions are compatible
```

The assessment retains the observed outcome separately from the universal claim:

- `:conditional`: all required progress declarations are present. The generated
  completion theorem still takes their Lean propositions as hypotheses.
- `:insufficient_assumptions`: required declarations are missing. Even an
  observed successful trace does not establish completion of all continuations.
- `:inconsistent_assumptions`: the success goal or an explicit no-failure premise
  contradicts an observed failure, including timeout observation before its handler.
- `:inconsistent_limits`: obvious required work is disallowed by the caps, for
  example no receive allowance or no inspections for a success goal.

These checks reject obvious contradictions. They do not prove that a behavior
satisfying all declared progress and applicability premises exists. Unknown
options or progress names, callbacks, retry declarations and timeout-as-budget
options are rejected rather than silently treated as evidence.

`completion.observed_outcome` is `:pending`, `:success`, `:timeout`,
`:peer_terminated` or `:decode_error`. Remaining allowance, active-action bound,
missing assumptions and external-progress status are reported independently.
`elapsed_time_bound` is always `:not_established`; `source_termination` remains
`:not_checked`.

## Building and verifying

Completion alone needs no cost profile:

```elixir
alias ReductionBounds.{RpcCompletionProof, ProofInput, Verification}

{:ok, candidate, proof} = RpcCompletionProof.build(
  conditions, initial_queue, timeline,
  goal: :success, progress: progress ++ [:no_failure_outcomes])
{:ok, postludes} = ProofInput.rpc_completion_postludes(proof)
reports = Verification.verify!(Lynx.Translation.new(postludes: postludes),
                              cache: true, shared_modules: true)
true = reports != [] and Enum.all?(reports, &(&1.status == :ok))
```

The builder checks concrete instrumented moves, their mailbox erasure, rank
consumption and initial active allowance. If declarations are sufficient, it
also emits `suppliedConditionalCompletion`; success additionally emits
`suppliedSuccessfulCompletion` with an explicit `NoFailure` premise. If premises
are missing or inconsistent, those instantiated completion claims are omitted.
Generic shared theorems remain conditional on their hypotheses.

To retain cost safety while assessing completion, use the existing cost profile:

```elixir
{:ok, candidate, proof} = RpcCompletionProof.build_with_cost(
  cost_profile, initial_queue, timeline, progress: [])
# candidate.completion.status == :insufficient_assumptions
# candidate.upper_bounds and cost-safety theorems remain available
{:ok, postludes} = ProofInput.rpc_completion_postludes(proof,
  cost: true, handler: candidate.server_contract.kind)
```

Verify these postludes through the same boundary. In both workflows builders
retain `lean_status: :not_checked`. Requested theorem names and declarations are
not successful verification reports, and successful verification does not
establish the external assumptions. Assumed server contracts stay assumed;
replayed handler contracts retain their evidence status and applicability scope.

The completion theory depends on the RPC/mailbox layer, independently of the
cost theory and Port completion. Named-module caching, dependency invalidation,
transitive axiom audits and the global job budget are shared. Port APIs and
proofs are unchanged. The [restricted source connection](rpc_source.md) adds finite normal-execution
correspondence; model completion must not be relabeled as source termination.

See the [public RPC workflow](rpc_workflow.md) for verification and result reporting.
