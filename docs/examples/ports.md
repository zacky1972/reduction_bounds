# Port models and supported clients

These examples check symbolic work. They do not execute a Port program,
measure reductions, establish response delivery, or establish a deadline.
Use the [installation instructions](../../README.md#installation) first.
Run the examples from the project root after compiling the project.

## Declare sizes, counts and event costs

A request-size bound does not establish a response-size bound. Supply both,
plus the structure size of traversed data and the total inspection/retry limits.
The caller is the Port owner, with at most one request outstanding.

```elixir
alias ReductionBounds.{PortProtocol, ProtocolConditions, ProtocolCost, ProtocolSize}

{:ok, conditions} = PortProtocol.conditions(
  data_bounds: Map.new([:request, :response, :message], fn slot ->
    {slot, %ProtocolSize{bytes: 8, structure: 16}}
  end),
  count_bounds: %{
    total_events: 30, submission_attempts: 4, submission_events: 8,
    resumptions: 3, retries: 3, receive_inspections: 8
  }
)

rules = for {{_, event} = context, rule} <- conditions.rules,
            elem(conditions.contract.events[event], 0) != nil, into: %{} do
  cost = Enum.reduce(rule.data, {:charge, :event_work}, fn slot, rest ->
    {:add, rest, {:add, {:data, slot, :bytes}, {:data, slot, :structure}}}
  end)
  {context, %{counter: List.first(rule.counts) || :total_events, cost: cost}}
end
{:ok, profile} = ProtocolCost.new(conditions, rules)
```

These cost functions are declared mathematical assumptions. Their concrete
runtime applicability is not checked. Every caller-owned context requires a
rule; environment observations do not acquire a work charge. Event costs are
capped using the independent size bounds and grouped by participant/counter.

## Verify a supplied model

Supply a registered event name or event struct for each occurrence. Observation
indexes are zero-based. Sizes must describe the actual data associated with
that occurrence; association with runtime data remains an assumption.

```elixir
names = [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode]
{:ok, observation} = ProtocolConditions.observe(%{request: [], response: [], message: []})
observations = Map.new(Enum.with_index(names), fn {_, index} -> {index, observation} end)

{:ok, result} = ReductionBounds.verify_port_model(profile, names, observations: observations)
result.lean_status
#=> :checked
result.verification_scope.kind
#=> :supplied_port_model
result.source_correspondence
#=> :not_checked
result.completion.observed_outcome
#=> :success
result.completion.theorem_status
#=> :not_established
{:ok, 1156} = ProtocolCost.evaluate(result.upper_bounds.caller.formula, %{event_work: 1})
```

The bound is universal for the model under its conditions, rather than just
the cost of the supplied success trace. Empty, waiting and failure prefixes
are included. Assigning one to a charge above is an example interpretation
of symbolic units, not a calibration to reductions or processor time.
The result gives no bound on port-side or external-program work.

## Request a conditional completion theorem

Completion needs hypotheses independent of a finite cost bound:

```elixir
completion = [
  limits: %{rejections: 2, resumptions: 3, inspections: 8},
  progress: [:caller_progress, :submission_progress, :resumption_progress, :response_progress],
  goal: :termination
]
{:ok, result} = ReductionBounds.verify_port_model(profile, names,
  observations: observations, completion: completion)
result.completion.theorem_status
#=> :checked_under_assumptions
result.verification_scope.conditional
#=> [:model_termination_under_progress]
result.completion.actual_completion
#=> :not_established
```

The hypotheses concern all modeled behavior, not only the observed prefix.
They require eventual caller work, submission outcomes, resumption or closure,
and response/closure/timeout handling within finite loop allowances. Arbitrary
finite idle delays remain possible. Success is stronger than termination:
`goal: :success` additionally requires `:no_failure_outcomes` in the progress
declarations. A final rejection, closure, timeout, or decode failure conflicts
with that successful-completion goal.

Missing progress produces `:insufficient_assumptions` with diagnostic entries,
while the cost bound remains checked. Inconsistent completion allowances or
an observed error conflicting with success also preserve the independent
cost result. No supplied completion theorem is reported in those cases.

## Verify supported target code

A source result requires a supported compiled client such as
`ReductionBounds.Fixtures.PortClient.request/2` in the test fixture. In an
application, compile your `Client` and `Helpers` modules normally. The accepted
client binds a static preparation call, branches on `port_command/3` with
`[:nosuspend]`, matches the response helper's data/closed/timeout result, and
calls a static decoder. See the [source fragment](../proof.md#connecting-a-supported-core-erlang-client-to-the-port-model).

```elixir
{:ok, bound} = ReductionBounds.infer_port_bound({Client, :request, 2}, profile,
  calls: %{
    prepare: {Helpers, :prepare, 1},
    reply: {Helpers, :await_reply, 1},
    decode: {Helpers, :decode, 1}
  })
bound.source_correspondence
#=> :checked
bound.verification_scope.kind
#=> :core_connected_port_client
bound.completion.scope
#=> :source_code
bound.completion.theorem_status
#=> :not_established
{:ok, 1181} = ProtocolCost.evaluate(bound.upper_bounds.caller.formula,
  %{event_work: 1, source_node: 1})
```

The example's source-node limit is 25, added to the protocol budget. Helpers'
value/work contracts remain explicit assumptions. Source correspondence is
checked for finite normally returning executions in the fragment. Source
prefixes inside a receive helper, helper exceptions and source termination
remain unverified. No placeholder empty model trace is presented as a source
execution. A conditional completion theorem checked separately for the model
does not become a termination theorem for the source client.

For IEx-defined targets retain the BEAM binary and pass `beam_binaries:
[beam]`; the target needs recoverable Core Erlang debug information. Unsupported
code returns a target and source path, rather than a checked model-only result.

## Read the result and diagnostics

| Field | Meaning |
| --- | --- |
| `upper_bounds` | Participant formulas with separate cost units |
| `conditions` | Explicit data, integer, count and state-specific requirements |
| `verification_scope.checked` | Claims checked in Lean |
| `verification_scope.conditional` | Checked completion theorems with hypotheses |
| `verification_scope.assumptions` | Call, progress, size and applicability assumptions |
| `verification_scope.trusted` | Trusted extraction, reification or processing |
| `verification_scope.unverified` | Remaining correspondence and timing obligations |
| `checked_theorems` | Shared and generated theorem names audited during this check |
| `completion` | Model/source scope, observed outcome when supplied, and unresolved progress |
| `diagnostics` | Missing conditions, conflicts and limitations |

Malformed inputs, missing cost/size/count contracts, exceeded cost-profile
limits, and inadmissible transitions are errors. The existing tagged tuple
reasons retain event indexes, counters, targets and source paths. Unknown event
names return `invalid_port_event`; unknown API keys return `unknown_options`.
Unknown nested completion keys return `unknown_port_completion_options`.
A timeout or failed Lean report returns an error and no checked result.

## Reproduce all supported workflows

```sh
mix test --only port_workflow
REDUCTION_BOUNDS_REPORT=1 mix test --only port_workflow
```

The second command prints formulas, conditions, outcome scopes, assumptions,
checked theorem names and diagnostics. Tests cover success, rejection,
closure, retries, unrelated-message inspections, suspension, application
timeouts, decoding failure, missing progress, inconsistent completion
conditions and source correspondence. Rejection tests cover missing sizes,
exceeded counts, wrong transitions, malformed events and forged flags.

Run the detailed certificate tests separately:

```sh
mix test --only protocol_model
mix test --only protocol_conditions
mix test --only protocol_cost
mix test --only port_completion
mix test --only port_source
```

These include altered certificates and unfinished proofs. For exact statements
and remaining limitations see the [proof reference](../proof.md#port-api-diagnostics-and-reproducible-evaluation).
