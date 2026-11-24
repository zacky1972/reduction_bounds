# Shared proof modules

All packaged proof families use named shared modules and checked artifact reuse.
The registry records stable module identities, source providers, direct imports,
and each workflow's required dependency closure. Assembly rejects duplicate
identities, cycles, and missing prerequisites before invoking Lean.

| Family | Shared theories | Request-specific declarations |
| --- | --- | --- |
| Integer and contracts | Integer size/analysis/cost/source, cost contracts, bound transfer | Reified programs, concrete contract declarations, certificates and transferred claims |
| Core and execution | Core fragment, struct rules, normalization, execution bounds | Extracted programs, normalization certificates, operation/callee charges and bounds |
| Protocol and Port | Protocol, conditions, cost, completion and source connection | Supplied profiles, observations, traces, source fragments, limits and completion assumptions |
| Lists and composition | Search and list rules, fixed membership/reversal models and composition helpers | Target function agreement, branch/path formulas, input contracts and caller bounds |
| Buffer and periodic models | Symbolic buffer paths, insertion/sequence models and periodic rules | Target stride, input conditions and user periodic contracts |

Packaged Lean files remain the source of their definitions. Fixed membership,
reversal and buffer helpers are produced by the existing generators, with no
second maintained copy. Their mathematical models quantify over symbolic charge
functions; concrete target and contract declarations remain generated per request.
The old membership/reversal helper names are retained through public aliases.
No private import mode is needed. The constructive decision instances for Port
conditions use ordinary constructor cases so their exported implementations do
not depend on private tactic-generated match helpers.

## Finalization and auditing

The boundary resolves every import before calculating versioned keys over each
complete module input, original source locations, effective Lean options, and
ordered dependency identities. A changed prerequisite invalidates its consumers.
Unknown external compiled imports disable caching for their consumers and
dependents. Lynx separately partitions artifacts by Lean version, compiled runtime
hashes, and options, and publishes successful artifacts atomically.

Each shared module and generated target is audited for transitive axiom
requirements. Existing final-theorem audits and source/callee replay checks
remain in place. Reports include every shared module followed by the target;
a shared failure cannot be hidden by selecting only the target report.

## Preparing a dependency closure once

A supervised process tracks in-flight preparation by finalized shared keys and
a context containing the build/cache location, toolchain identity, effective
Lean environment and compiled dependency hashes. The first caller owns the
missing shared keys and runs its ordinary verification request. An overlapping
caller waits without holding any other preparation keys. Independent closures
can proceed immediately; requests whose shared dependencies are already ready
can also proceed concurrently.

Readiness is recorded only for successful shared reports. A target failure does
not discard successfully checked theories. Shared failures and exceptions clear
failed readiness, and monitored owner death releases in-flight keys so another
caller can retry. A cancelled waiter is removed and cannot later start a runner.
A supervised task owns the runner port under the [global job budget](job_budget.md).
Caller cancellation terminates that task. Waiting is included in the existing
per-target deadline.

Readiness is advisory. Every request still supplies its dependency-ordered
closure to the pinned runner, which loads the matching checked artifacts and
returns all module reports. There is no saved Lean environment or persistent
runner pool. Different OS processes may duplicate compilation; atomic artifact
publication preserves correctness. Regression tests exercise both concurrent
callers in one VM and publication from independent VMs.

The runner processes modules sequentially inside one request. This stage reuses
checked dependency closures and coalesces overlapping cold work. It does not
change test concurrency defaults. A separate global verification job budget
now limits concurrent runner calls after preparation coordination.

## Controls and measurements

The default is named shared modules with shared and target caching enabled.
Use `REDUCTION_BOUNDS_PROOF_CACHE=shared` to cache only common theories,
`REDUCTION_BOUNDS_PROOF_CACHE=off` to recheck every module, or
`REDUCTION_BOUNDS_PROOF_MODE=embedded` to assemble the same sources into the
original postlude representation. Bypassed requests carry no persistent keys
and do not acquire preparation leases. Focused cache tests explicitly exercise
all modes, independently of these environment defaults.

Benchmark completion events include `coordination.mode` and
`coordination.wall_ms`. The latter covers identity lookup and waiting for a
preparation lease; it is also included in request runner wall time. Consequently,
the non-module remainder is not a pure process-startup measurement. The summary's
`coordination_wall_ms_sum` is unavailable for older events without this field.
See [benchmarking](benchmarking.md) for the timing and memory limitations.

The [all-family measurements](baselines/issue8-all-proofs.md) record both warm
benefits and overhead in smaller workflows.
