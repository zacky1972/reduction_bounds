# Public RPC verification workflow

Use the public APIs to build proofs, select their packaged dependencies and
submit them through the existing verification boundary. Results become checked
only after nonempty successful reports include the final target proof. Errors,
timeouts and skipped reports do not produce checked results.

## Model with costs

Construct a `cost_profile` using the [cost guide](rpc_cost.md), then supply the
initial reified queue and the [mailbox timeline](rpc_mailbox.md):

```elixir
{:ok, result} = ReductionBounds.verify_rpc_model(
  cost_profile, initial_queue, timeline,
  completion: [
    goal: :success,
    progress: [:client_progress, :request_progress, :server_progress,
               :response_progress, :no_failure_outcomes]
  ],
  timeout: 300_000)
```

`result.lean_status` is `:checked` after verification. Participant budgets remain
conditional on the declared input, size/count, cost-envelope and ledger contracts.
Missing progress keeps cost safety usable while reporting
`completion.theorem_status: :not_established`. A completed example does not prove
all continuations finish. Inconsistent progress/failure assumptions are reported
separately; a valid cost certificate does not validate those assumptions.

For mailbox conditions and completion without rates or a handler cost contract:

```elixir
{:ok, result} = ReductionBounds.verify_rpc_conditions(
  conditions, initial_queue, timeline, timeout: 300_000)
```

This result does not contain participant budgets or claim cost safety.
Both APIs accept the existing `timeout`, `max_concurrency` and `lean_options`
settings, plus `completion`. Completion declarations are those documented in the
[completion guide](rpc_completion.md). Proof mode, cache policy and the global
Lean job budget retain the existing environment controls.

## Restricted source

Use the [documented source fragment](rpc_source.md), with explicit reply/decode
helper declarations:

```elixir
{:ok, result} = ReductionBounds.infer_rpc_bound(
  {Example.Client, :request, 4}, cost_profile,
  calls: %{
    reply: {ReplyHelpers, :await_reply, 3},
    decode: {ReplyHelpers, :decode, 1}
  },
  timeout: 300_000)
```

For an in-memory compiled client, also pass `beam_binaries: [...]` containing its
debug information. Those binaries are used for source extraction, without
translating unrelated BEAM definitions. The same concurrency, timeout and Lean
settings apply. Unknown proof overrides, reports and unsupported option forms
are rejected. Unsupported syntax retains the target and structural Core path;
it does not fall back to a model-only result labeled as source verification.

The result checks the finite normal reified-Core connection and formula under
contracts. `source_correspondence: :checked_under_contracts` does not establish
helper implementations or runtime mailbox association. Their certificates and
applicability remain explicit obligations. The supplied request identifies the
source inputs; this is not automatic inference over all similarly sized inputs.
No target execution or observed source outcome is reported.

## Reading evidence

| Field | Meaning |
| --- | --- |
| `lean_status` | Successful verification reports, distinct from builder-only candidates |
| `reports`, `checked_theorems` | Actual reports and audited theorem names |
| `verification_scope.checked` | Checked structural/model facts or conditional source theorems |
| `verification_scope.conditional` | Model completion under progress, or source claims under helper/association contracts |
| `verification_scope.assumptions` | Applicability conditions that verification does not establish |
| `verification_scope.trusted` | Model selection, abstraction, extraction/reification and serialization boundaries |
| `unverified`, `unsupported` | Unresolved guarantees and explicitly unsupported features |
| `diagnostics` | Missing/inconsistent completion assumptions and source/helper obligations |
| `upper_bounds` | Separate model client/server budgets, when a cost profile is supplied |
| `client_source_bound` | Additional source-node formula under compatible disjoint accounting |

An assumed server bound stays `:assumed`. A replayed handler becomes
`:checked_under_contracts` only after its original evidence is replayed and all
reports succeed. Its callee assumptions, source association and runtime
applicability are retained.

For model results, `completion.theorem_status` becomes
`:checked_under_assumptions` only when progress declarations support the generated
claim. `completion.actual_completion` stays `:not_established`. Success additionally
requires failure exclusion. Source results always report source completion as
`:not_established`; a model completion theorem never establishes source totality.

The supported prototype is single-attempt ordinary same-node RPC. Native source
receive, monitored source clients, retries, multiplexing, priority/distributed
behavior and receive optimizations require further semantic extensions. Model
monitors remain supported. Helper bodies, arbitrary unfinished source prefixes,
source totality, concrete runtime charging and wall-clock guarantees remain
outside the checked source scope.

All three workflows reuse the existing target timeout handling, dependency-aware
module cache, coalesced preparation, transitive axiom audits and per-VM job budget.
No additional RPC runner, admission queue or global configuration mutation is
introduced. The low-level builders remain available and retain `:not_checked`;
the public APIs perform the verification and report construction.
