# Compare cost contracts and reuse a verified bound

## Supported analysis and proof scope

The analyzer recovers Core Erlang from BEAM debug information. Supported
fragments have reusable cost rules, explicit input conditions, and Lean
proofs; unsupported expressions and unresolved contracts are reported.
The integer fragment supports size-dependent charges, bindings, branches,
static calls with contracts, and finite recursive derivations.

The following public APIs distinguish the relevant proof scopes:

| API | Checked result |
| --- | --- |
| `infer_integer_cost_bound/2` | A source-related bound under arbitrary nondecreasing charges and the stated call contracts |
| `compare_cost_contracts/3` | Declarative charge and budget ordering, plus a conditional execution comparison without selecting a target |
| `transfer_integer_bound/3` | A rechecked target bound reused from its source contract B under a smaller destination contract A |

Comparison arguments run from smaller to larger. Transfer arguments are an
existing bound carrying B and the destination A. Transfer re-extracts the
target, rechecks any reused callee bounds, and verifies both the original
derivation and comparison evidence. The resulting formula is evaluated
under B; its checked numeric value is `upper_bound_value`.

Both comparison and transfer results include `verification_scope`, with
`checked`, `assumptions`, `trusted`, and `unverified` fields. Their
`checked_theorems` identify the Lean declarations audited. A contract named
`:jit` or `:interpreter` supplies no evidence about that execution mode.

## Interactive example

This example can be run in `iex -S mix` from the project root after
installing the Lean prerequisites.

```elixir
alias ReductionBounds.{CostContract, IntegerSize}

{:module, ContractDemo, beam, _} =
  defmodule ContractDemo do
    @compile :debug_info
    def square(x), do: x * x
  end

functions_b = Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
functions_a = Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
{:ok, b} = CostContract.new(id: :source, functions: functions_b)
{:ok, a} = CostContract.new(id: :destination, functions: functions_a)

{:ok, bound} =
  ReductionBounds.infer_integer_cost_bound({ContractDemo, :square, 1},
    input_sizes: [%IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}],
    cost_contract: b,
    beam_binaries: [beam]
  )

{:ok, comparison} = ReductionBounds.compare_cost_contracts(a, b)
{:ok, transferred} =
  ReductionBounds.transfer_integer_bound(bound, a, beam_binaries: [beam])

transferred.upper_bound_contract
#=> :source
transferred.upper_bound_value
transferred.verification_scope
transferred.checked_theorems
```

For contracted calls, transfer requires `callee_correspondence: :shared`
for a common mathematical external model, or a Lean proof of value and
actual-cost correspondence between two external models. Source callee
contracts remain explicit assumptions. Missing correspondence is an error.
Transfer also checks narrower `input_sizes` when supplied. See the
module documentation and [proof documentation](../proof.md) for these
conditions, diagnostic examples, and the formal guarantees.

To reproduce the public workflow evaluation, including variance and CRC
expressions, and print the formulas, conditions, and checked theorem names:

```sh
REDUCTION_BOUNDS_REPORT=1 mix test --only cost_contract_workflow --trace
```

This evaluates the symbolic proof workflow; it does not measure runtime
reductions or processor time.
