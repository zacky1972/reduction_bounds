# Roadmap

The current development scope is independent of a particular Erlang VM
implementation. The [examples index](examples.md) and
[proof reference](proof.md) describe the supported cases and the exact
claims checked for each model.

## Established prototype capabilities

The original evaluation targets now have model-level analyses:

- List membership and conditional reversal reuse traversal and reversal
  cost rules and contracts.
- CircularBuffer insertion has bounds for one call and sequences,
  including calls that trigger list reversal. The state model also has
  proofs against a bounded FIFO specification.
- Supported integer code has size-dependent symbolic costs, finite
  recursive derivations, contract comparison, and verified bound reuse.
- The external Port model has finite-trace and prefix cost safety and
  conditional completion under explicit progress and loop conditions.
- A finite normally returning Core Erlang client can be connected to that
  model under explicit helper contracts. Public results distinguish model
  theorems from source correspondence and unresolved completion obligations.
- The public proof workflow records assumptions, checked theorem names,
  trusted processing, and unverified runtime claims.
- An initial RPC model checks supplied single-attempt protocol traces and
  request/monitor correlation on the shared communication foundation. It does
  not itself analyze mailbox behavior or derive RPC cost/completion bounds.
- A separate RPC mailbox layer replays ordinary-message matching, queue
  retention, cursor behavior, timeout eligibility and explicit size/count
  conditions. It supplies mailbox semantics for the separate cost and completion
  layers; source/runtime correspondence remains later work.

- Conditional RPC cost safety now separates client and server budgets and
  replays unary integer handler contracts with an independent server frame.
  Cost envelopes, future count bounds and runtime work correspondence remain
  explicit assumptions; see the [cost guide](examples/rpc_cost.md).

- Conditional RPC model completion now uses a mailbox/control rank and explicit
  progress premises over all admitted continuations. Success separately excludes
  timeout, peer termination and decoding failure. Suspended cost safety does not
  require progress; see the [completion guide](examples/rpc_completion.md).

These descriptions refer to the checked models and supported fragments;
see the proof reference for the remaining correspondence obligations.

## Further model development

- Build a supported RPC source connection on the checked
  [mailbox conditions](examples/rpc_mailbox.md) and conditional model theorems.
  Repeated RPC attempts require explicit retry and duplicate-execution contracts.

- Extend the supported program fragments and reusable contracts while
  continuing to report unsupported operations and unresolved obligations.
- Extend Port source correspondence to unfinished prefixes, native receive,
  exception handling and helper implementations. Source termination requires
  further totality and progress arguments; the model completion theorem alone
  does not provide them.
- Improve automatic derivation and document which input conditions,
  invariants, and size measures users must supply.
- Extend source-to-model correspondence where the current proofs still
  start from a separately checked or recognized state model.

## Later implementation-specific work

- Relate symbolic charges to reductions for specified runtime builds and
  execution modes, including built-ins that yield and resume.
- Investigate analysis directly from BEAM instructions, with the longer-term
  goal of accepting modules with stripped debug information. This requires
  instruction-level execution and reduction-accounting models.
- Evaluate runtime reduction counts and timing separately from the
  VM-independent symbolic proofs.

These implementation-specific directions do not form part of the current
VM-independent guarantees. Publishing an open-source prototype does not
establish its applicability to an arbitrary runtime configuration.

## Verification throughput follow-ups

Shared checked artifacts, preparation coordination and bounded test concurrency
are implemented. Reusable runner sessions and cold dependency scheduling remain
conditional follow-ups. The current backend uses one-shot calls and sequential
dependency-ordered module processing. See the
[runner optimization review](runner_optimization_review.md) for the measurements,
supported-API and correctness gates required before changing that backend.

The [Issue 8 status](issue8_status.md) records completed concurrency/cache work
and the successful reference-Mac calibration. The [retained defaults](verification_defaults.md)
distinguish the initial Mac profile (4 jobs, 2 Lean threads) from the portable
fallback; neither is claimed to be universally optimal.
