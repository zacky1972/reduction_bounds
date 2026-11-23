# Proofs of symbolic cost bounds

## Integer value ranges and magnitude sizes

`IntegerSize` describes a set of mathematical integers. Its three
components constrain the same value: a finite lower endpoint requires
`lower <= value`, a finite upper endpoint requires `value <= upper`,
and a known magnitude bound requires `abs(value) < 2^bits`.
The endpoints are inclusive and the magnitude limit is strict.
An unbounded endpoint or unknown magnitude adds no constraint.
All components are conjoined. Contradictory constraints denote the
empty set; they do not cause a constraint to be discarded.
`valid?/1` checks field types, while `contains?/2` implements membership
and rejects malformed representations and non-integer inputs.

In `priv/lean/reduction_bounds/IntegerSize.lean`, `Bounds` represents
missing components with `Option.none`, and `Holds` defines the
represented set over Lean's `Int`. The magnitude predicate uses
`value.natAbs < 2 ^ width`, without a sign bit or a machine-word limit.
`containsCorrect` proves that the Lean Boolean membership test equals
this predicate. The component projection theorems recover each stated
constraint. `unconstrained` admits every integer, `zeroMagnitude`
admits exactly zero, and `reversedRange` admits no integer when the
upper endpoint is below the lower endpoint.

Run the tests with:

```sh
mix test test/reduction_bounds/integer_size_test.exs test/reduction_bounds/integer_size_proof_test.exs
```

The proof test loads the packaged Lean definitions through Lynx,
checks the generic theorems for unexpected axioms, compares the Lean
and Elixir predicates on signed boundary cases and values around
`2^200`, and confirms that Lean rejects an invalid membership claim.
These finite comparisons check the serialization and examples; they
are not a universal proof of the Elixir implementation. The generic
theorems apply to the Lean definitions. Basic arithmetic size propagation
is described below, followed by program inference and size-dependent
operation-cost contracts. No immediate-integer threshold or ERTS
reduction accounting is assumed here.

### Unknown information and unreachable states

`IntegerSize.unknown/0` returns the unconstrained `%IntegerSize{}` and
admits every integer. `IntegerSize.unreachable/0` returns the distinct
atom `:unreachable` and admits no integer. Both are valid representations;
missing size information must not be interpreted as an impossible state.

`normalize/1` converts exactly the empty constraint sets to
`:unreachable`. Satisfiable structs are returned unchanged, and
normalizing `:unreachable` returns `:unreachable`. `unreachable?/1` tests
semantic emptiness through this normalization. Malformed field values
remain errors rather than being silently classified as unreachable.
Membership in `:unreachable` is false for every integer.

The emptiness check constructs a candidate from the interval endpoints:
use zero when neither endpoint is known, clamp zero toward a finite
endpoint when only one is known, and use `max(lower, min(0, upper))`
when both are known. If any integer satisfies the range and magnitude
constraints, this candidate satisfies them too. It is therefore enough
to test this single candidate, even for one-sided ranges or magnitudes
larger than a machine word. This check does not enumerate the interval.

Lean's `Domain` adds `.unreachable` alongside `.bounded bounds`.
`Domain.Holds` assigns the former the empty set and the latter the
existing `Holds` predicate. `witnessHolds` proves the candidate property.
`normalizeSound` proves membership equivalence before and after
normalization for every integer. `normalizeUnreachableIff` proves that
the normalized result is unreachable if and only if no integer satisfies
the original constraints. `normalizeIdempotent` proves that a second
normalization changes nothing. `unknownHolds`, `unreachableHolds`, and
`unknownNotUnreachable` establish the distinction between the two states.
The test's axiom audit includes these theorems.

ExUnit tests exercise partial bounds, zero, conflicting magnitude bounds,
large integers, and every combination of endpoints from -5 through 5 or
unbounded with magnitude bounds 0 through 3 or unknown. The proof test
compares Elixir and Lean normalization results and membership, and checks
that Lean rejects declaring unknown information unreachable. These tests
extend the two integer-size test files listed above. Finite comparisons
do not establish universal correctness of the Elixir implementation.
The domain is not yet connected to branch conditions in the analyzers;
a claim that actual program control cannot reach a branch will also need
proof that the constraints describe all states at that point.

### Constants and arithmetic size propagation

The common integer domain now provides `from_integer/1`, `add/2`,
`subtract/2`, and `multiply/2`. For every pair of integer operands
satisfying the supplied descriptions, the result description contains
the corresponding arithmetic result. These are domain operations;
they are not yet applied automatically to extracted Core Erlang.

For a constant `z`, `from_integer(z)` has the exact interval `[z, z]`
and the smallest magnitude width with `abs(z) < 2^width`. Zero has
width zero. Let `[L1, U1]` and `[L2, U2]` denote finite operand
intervals, and let `w1` and `w2` be known magnitude bounds.

| Operation | Interval rule | Magnitude bound |
| --- | --- | --- |
| Addition | `[L1 + L2, U1 + U2]` | `max(w1, w2) + 1` |
| Subtraction | `[L1 - U2, U1 - L2]` | `max(w1, w2) + 1` |
| Multiplication | Minimum and maximum of `L1*L2`, `L1*U2`, `U1*L2`, `U1*U2` | `w1 + w2` |

For addition and subtraction, an endpoint is unknown if a required
operand endpoint is unknown. The magnitude result is unknown if either
operand magnitude is unknown. For multiplication, this first rule uses
unbounded endpoints unless all four operand endpoints are finite. It
still propagates known magnitude bounds. A valid operand with magnitude
zero, or with both endpoints zero, gives an exact zero product when the
other operand is not unreachable. The one-sided multiplication rule
is deliberately conservative and can be refined later.

Both operands are validated and normalized before every operation.
If either denotes the empty set, the result is `:unreachable`, including
zero times an unreachable operand. Malformed information remains an
error, even if the other operand is unreachable. Result normalization
preserves the represented set.

The domain does not track correlations between operands. Subtracting
`[1, 3]` from the same description therefore gives `[-2, 2]` rather
than inferring zero. Constant cancellation can still produce the exact
interval `[0, 0]`, while the propagated magnitude bound is deliberately
coarse. The analysis keeps descriptions of intermediate values separate:
a zero final result does not reduce the bound on an earlier product.
For example, squaring `2^200` has exact value `2^400` and a propagated
magnitude bound of 402, even if subtracting that product from itself
later produces zero.

In Lean, `magnitudeBitsCorrect` and `magnitudeBitsMinimal` characterize
the constant width, and `singletonExact` characterizes its represented
set. The endpoint and magnitude lemmas establish the arithmetic rules
for all integer values. `productInterval` bounds the signed product by
the four corners, and `zeroValue` justifies the zero shortcut.
`boundsAddSound`, `boundsSubtractSound`, and `boundsMultiplySound`
combine interval and magnitude constraints. `binarySound` lifts these
rules through input and output normalization. `addSound`,
`subtractSound`, and `multiplySound` state the final domain guarantees
under operand membership assumptions. The same axiom audit covers
all these theorems.

The existing two integer-size test files also cover carry bits,
negative products, one-sided bounds, unreachable inputs, invalid inputs,
large intermediate products, and cancellation. Finite-domain tests
check every admitted operand pair in the chosen small grid. The proof
test compares the Elixir and Lean transfer results for all combinations
of its example descriptions and rejects false claims about a missing
carry bit and unrelated operands. These comparisons test agreement on
examples; the universal theorems apply to the Lean definitions.

The following sections cover constant shifts, low-bit masks, XOR,
branch refinement, and propagation through supported Core Erlang bindings.
The separate integer cost entry point below adds static call contracts,
finite recursion with invariants, and size-dependent cost functions. No runtime word size,
small-integer boundary, or ERTS reduction formula is fixed here.

### Constant left shifts and low-bit masks

`shift_left/2` accepts a size description and a fixed nonnegative integer
shift amount `k`. Each finite endpoint is multiplied by `2^k`; missing
endpoints remain unbounded. A known magnitude bound `w` becomes `w + k`,
while an unknown bound stays unknown. Positive scaling preserves the
order of negative as well as positive endpoints. A known zero input
remains exact zero. The modeled value is `shiftValue z k = z <<< k`.
`shiftValueMultiply` relates it to `z * 2^k` using Lean's signed shift
semantics. `lowerShiftSound`, `upperShiftSound`, and `shiftBitsSound`
prove the component rules, and `boundsShiftLeftSound` combines them.

`mask/2` retains the low `k` bits, for any signed integer input. Its
mathematical value is the nonnegative remainder `maskValue z k = z % 2^k`
with Euclidean division. This defines a low-bit mask without choosing
a machine word size. In particular, masking `-1` gives `2^k - 1`;
it does not retain the original magnitude bound of one bit. The general
result interval is `[0, 2^k - 1]` and its magnitude bound is `k`.
A known zero input, or a zero mask width, gives exact zero. This first
rule deliberately drops other range information from the input.

`maskRange` proves the nonnegative range, `maskResidue` proves that the
remainder preserves the residue modulo `2^k`, and `maskUnique` proves
uniqueness under those two conditions. `maskMagnitudeBound` gives the
width bound. `maskInRange` proves that a value already in range is
unchanged, `maskNegativeOne` handles `-1` for every width, and
`maskAfterFullShift` proves that shifting by `k` and then retaining only
`k` low bits gives zero. `boundsMaskSound` proves the size rule for this
mathematical masking operation.

Both APIs reject negative, fractional, or unknown shift amounts and mask
widths; their width argument is a constant, not a size description.
They validate and normalize the input and preserve unreachable states,
including when the width is zero. The shared `Domain.unary` rule applies
normalization on input and output. `unarySound` proves that it lifts a
sound operation on `Bounds` to the domain containing unreachable states.
`shiftLeftSound` and `maskSound` specialize that rule.

The unit tests compare actual `Bitwise.bsl/2` and `Bitwise.band/2` results
with the mathematical value operations and check that the propagated
bounds contain them. Cases include negative values, widths zero and 64,
values around `2^200`, partial ranges, invalid widths, and empty inputs.
The proof test also compares those actual values and the Elixir transfer
results with the Lean definitions, audits the new theorems, and checks
that Lean rejects dropping shifted bits or retaining a negative masked
result. These finite comparisons do not constitute a universal proof of
the Elixir primitives or a translation theorem for an Erlang built-in.
The universal size theorems cover the stated Lean value models and make
no cost claim.

Size descriptions are immutable and remain separate at each operation.
For example, shifting `2^100` by 100 produces `2^200` with width bound
201. Retaining its low 64 bits then produces a value bounded by 64 bits,
which is zero for this concrete input. The later mask does not reduce
the recorded bound for the earlier shifted intermediate.

The two integer-size test files listed above reproduce these checks.
These rules introduce no immediate integer boundary or concrete ERTS
reduction charges.

### Signed XOR and constant right shifts

`bit_xor/2` propagates a conservative magnitude bound for signed XOR.
With operand bounds `a` and `b`, the result has magnitude bound
`max(a, b) + 1`. Its interval endpoints are unbounded. If either
magnitude is unknown, the result magnitude is unknown. The extra bit
is necessary for this uniform signed rule: `3 XOR -1 = -4`.
`xorValue` defines the operation using natural-number XOR and the
signed complement representation; `xorMagnitude`, `boundsXorSound`,
and `xorSound` establish the size bound for every pair of admitted
mathematical integers.

`shift_right/2` accepts a fixed nonnegative amount `k`. It divides
finite endpoints by `2^k` with floor rounding. The result retains the
original magnitude bound, a deliberate conservative choice that also
covers negative values such as `-1 >> k = -1`. `rightValue` uses
Lean's signed right shift. `rightMagnitude`, `divideMonotone`,
`boundsShiftRightSound`, and `shiftRightSound` justify the rule.
Both operations validate and normalize operands and preserve
unreachable information. The tests compare actual signed Elixir
operations with the Lean definitions on boundary cases; these finite
checks are not a proof of an Erlang built-in implementation.

### Comparison assumptions and joins

`assume(size, comparison, constant, truth)` refines an integer
under a comparison with a constant `k`. The supported comparisons
are `:lt`, `:le`, `:eq`, `:ne`, `:ge`, and `:gt`. For example,
the true branch of `x < k` sets an upper bound of `k - 1`, and
the false branch sets a lower bound of `k`. The true branch of
`x == k` intersects both endpoints with `k`. Negated equality
cannot in general be represented as one interval, so it leaves
the description unchanged. `:ne`, `:ge`, and `:gt` use the
corresponding complementary rules. Normalization turns contradictory
branch constraints into `:unreachable`. `assumeSound` proves that
every admitted value satisfying the selected condition remains admitted.

`join/2` covers the union of two alternatives: take the minimum
finite lower endpoint, maximum finite upper endpoint, and maximum
known magnitude bound. An absent endpoint or unknown magnitude on
either side makes that component unknown. `:unreachable` is the
identity. `joinLeftSound` and `joinRightSound` prove inclusion of
both alternatives. The domain does not track operand correlations
or excluded interior points. Finite endpoints do not automatically
supply a magnitude bound when `magnitude_bits` is unknown.

### Size propagation through a Core Erlang fragment

`ReductionBounds.infer_integer_sizes/2` extracts a target's Core Erlang
from its BEAM debug information and decodes a non-recursive integer
fragment. It supports integer literals, variables, single-variable
bindings, sequencing of integer expressions, unary signs, addition,
subtraction, multiplication, XOR, constant nonnegative shifts, low-bit
masks, and Boolean branches comparing an integer expression with a
constant. Constants on either side of a comparison are supported.
An expression used as a test operand is bound to a fresh variable
before branch refinement. Other function calls, recursion, variable
shift amounts, general masks, and unsupported conditions are rejected
with the target and a location in the decoded expression.

```elixir
alias ReductionBounds.IntegerSize

{:ok, analysis} =
  ReductionBounds.infer_integer_sizes({MyModule, :update, 1},
    input_sizes: [%IntegerSize{lower: -2, upper: 4, magnitude_bits: 3}]
  )
```

For `update(x)` defined as `y = x * 3` followed by
`if y < 0, do: y - 1, else: y + 1`, the returned result has
range `[-7, 13]` and magnitude bound 6. Omitted input descriptions
are unknown; supplied descriptions must occur in argument order.
`beam_binaries` supports modules compiled only in memory, as for
other inference APIs. If an input is unreachable, the entire input
state is unreachable, including for a constant-returning body.

The result exposes `input_sizes`, `result_size`, and an ordered
`intermediates` list. Each row records its expression path, operation,
and inferred size. Operation rows also record operand sizes; rows
inside a branch include its comparison and refined description.
`unresolved_sizes` identifies rows without magnitude bounds. Intermediate
sizes remain recorded before later masking or cancellation. The CRC-style
fixture therefore reports a 16-bit shifted intermediate and a conservative
17-bit XOR intermediate before returning an 8-bit masked result.

`IntegerAnalysis.lean` defines a concrete mathematical integer
evaluator and an abstract interpreter for the same expression datatype.
`Covers` relates an input environment to its size descriptions.
`bindCovers` proves preservation when a binding receives a value admitted
by its inferred description. `refineCovers` proves preservation on a
selected comparison branch. The structural theorem `inferSound`
connects these rules: for every environment satisfying `Covers`,
evaluation returns a value admitted by the inferred result description.
The evaluator terminates by structural recursion on this finite,
non-recursive expression syntax.

For each target, `targetIntegerSizeCorrect` checks that the Elixir
candidate equals the Lean interpreter's inferred result.
`targetIntegerTraceCorrect` checks the complete ordered list of
intermediate expression paths and size descriptions against the Lean
trace. Additional descriptive metadata is not part of this equality.
`targetIntegerSizeBound` instantiates the universal soundness theorem
under the supplied input conditions. The common verification path records
these theorem names and audits their dependencies; only `propext`,
`Classical.choice`, and `Quot.sound` are permitted as axioms.

The proof starts at the reified integer fragment. Extraction from
BEAM debug information and the Elixir decoder remain trusted; this
change does not prove correspondence with the original Core Erlang
or with a Lynx-translated target. The result explicitly reports
`proof_scope: :reified_integer_fragment`, `value_agreement: :not_checked`,
`termination: :structural_model`, and `cost_model: :not_analyzed`.
The result is size information, not a bound on runtime reductions or
execution time. The separate integer cost entry point below adds size-dependent cost
functions, bounded recursion, and contracts for call results; those
features do not change this older entry point's proof scope.

The following commands reproduce the domain tests, Lean comparisons,
compiled-fixture checks, and rejection of falsified results and traces:

```sh
mix test test/reduction_bounds/integer_size_test.exs \
  test/reduction_bounds/integer_size_proof_test.exs \
  test/reduction_bounds/integer_analysis_test.exs
```

## Integer sizes connected to symbolic costs

`ReductionBounds.infer_integer_cost_bound/2` connects integer size
information to the symbolic cost rules. It is a separate entry point
from `infer_integer_sizes/2`: the latter retains its original,
non-recursive interpreter and trusted decoder boundary. The new entry
point checks a lowering certificate from a reified supported Core
fragment and a cost derivation, including finite recursive expansions.

### Operation cost contracts and applicability

`ReductionBounds.CostContract` identifies the operation-cost declaration
used with the integer fragment. It is distinct from a callee's
`call_contracts` entry. The default declaration uses symbolic functions,
cost unit `:symbolic_work`, value semantics `:core_integer_v1`, and
charge-event profile `:integer_cost_v1`. These profiles currently accept
all pairs of natural parameters; narrower domains and arbitrary state
parameters are not supported by this declaration interface.

The parameter registry records magnitude widths for binary arithmetic,
XOR, and comparisons; input width and constant amount for shifts;
input width and constant mask width for masks; and two unused zero
parameters for local fixed charges. Auxiliary names appearing in callee
budgets are also declared. In the default symbolic contract their
parameters are labeled `:callee_parameter_1` and `:callee_parameter_2`;
their interpretation is a callee-contract assumption. A user declaration
must include the required auxiliary names and their parameter labels.

Functions can be symbolic or supplied as declarative expressions built
from natural constants, `:left`, `:right`, addition, multiplication, and
maximum. A concrete function map must cover exactly the declared names.
Negative constants, executable Elixir functions, unsupported expressions,
and unsupported profiles are rejected. `CostContract.evaluate/3`
evaluates a declared expression on natural arguments; it produces a
number, not a proof certificate.

For example, after compiling a supported module, use:

```elixir
alias ReductionBounds.{CostContract, IntegerSize}

expr = {:add, 1, {:mul, :left, :right}}
functions = Map.new(CostContract.operations(), &{&1, expr})
{:ok, contract} = CostContract.new(id: :example, functions: functions)

{:ok, result} =
  ReductionBounds.infer_integer_cost_bound({MyModule, :update, 1},
    input_sizes: [%IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}],
    cost_contract: contract
  )

result.cost_contract
result.applicability
CostContract.evaluate(contract, :multiplication, [8, 9])
#=> {:ok, 73}
```

The result records the declaration in `cost_contract`. Its `applicability`
field records the cost unit, profiles, parameter meanings, actual input
descriptions, supplied recursive invariant, inferred recursive argument
domains, and callee assumptions. Omission preserves the existing symbolic
inference and records a default contract. This option does not change
the symbolic `upper_bound` or supply an evaluated numeric bound.

The existing Lean cost theorem remains quantified over arbitrary
nondecreasing functions. `size_monotonicity: :assumed` records that
premise. `contract_instantiation: :not_checked` explicitly states that
the declared concrete functions have not been instantiated and checked
in Lean. Declarative syntax validation and Elixir evaluation must not
be reported as that proof. A separate comparison API now checks
expression monotonicity and function and budget ordering, as described
below. The bound-transfer API below additionally instantiates and rechecks
concrete contracts for the supported integer fragment.

Contract identifiers and cost-unit labels are declarations. Naming a
contract `:jit`, or its unit `:reductions`, supplies no implementation
evidence. Both the result and applicability report
`runtime_correspondence: :not_checked`. The actual correspondence to
ERTS charges, execution modes, and timing remains an external obligation.

Run the declaration tests and the existing inference integration tests:

```sh
mix test test/reduction_bounds/cost_contract_test.exs \
  test/reduction_bounds/integer_cost_bound_test.exs
```

### Lean checks of cost-function and budget ordering

`ReductionBounds.compare_cost_contracts(smaller, larger, options)`
checks a pointwise ordering between two declarative contracts. The
argument direction is smaller to larger. Both declarations are validated
and must have the same cost unit, semantics, charge events, parameter
domain, operation names, and parameter meanings. These compatibility
checks are performed by Elixir and reported as such; they are not
runtime-correspondence proofs. Symbolic functions must first be replaced
by declarative definitions. Restricted domains are not supported.

`CostContract.lean` defines the shared natural-valued expression
semantics. `Expr.monotone` proves that every expression in the supported
grammar is nondecreasing in both natural parameters. This property is
distinct from the ordering of two different expressions.

The Elixir checker builds an `ExprLe` certificate for each operation.
Its rules cover reflexivity, zero, constant inequalities, componentwise
addition, multiplication and maximum, extension by nonnegative summands
or maximum alternatives, and elimination of a maximum when both sides
are bounded. `ExprLe.sound` proves every such derivation valid for all
natural parameters. The search is deliberately incomplete: it can
report `unresolved_cost_order` even for a true inequality, such as a
commuted sum. It does not declare unresolved inequalities false, and
never uses finite samples as a universal ordering proof.

The generated `functionCertificate` aligns the functions in one explicit,
shared operation registry. The first 13 entries now follow the numeric
operation order used by `IntegerCost.Runs`; auxiliary names follow in sorted
order. The integer bound generator uses the same core registry.
`FunctionsLe.sound` proves pointwise ordering
of the resulting charge assignments. Operations beyond that registry
have zero cost in both assignments. `functionsMonotone` establishes the
existing `IntegerCost.MonotoneCharges` property for each assignment.

`budgetMonotone` reuses `IntegerCost.Budget`: leaves respect the charge
ordering, sequential addition preserves it, and maximum preserves it
at alternatives. The generated `allBudgetOrdering` theorem applies to
every budget in that datatype, not only a supplied example. An optional
`budget` uses the existing integer formula syntax: zero, cost leaves
with two natural arguments, addition, and maximum. Unknown operation
names, negative arguments, symbolic variables, and unsupported forms
are rejected. `suppliedBudgetValues` checks both Elixir-computed values
against Lean evaluation, and `suppliedBudgetOrdering` specializes the
generic inequality to that budget.

```elixir
alias ReductionBounds.CostContract

functions_a = Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
functions_b = Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
{:ok, a} = CostContract.new(id: :a, functions: functions_a)
{:ok, b} = CostContract.new(id: :b, functions: functions_b)

{:ok, comparison} =
  ReductionBounds.compare_cost_contracts(a, b,
    budget: {:add, {:cost, :addition, [8, 9]}, {:cost, :binding, [0, 0]}}
  )

comparison.budget_values
#=> %{smaller: 10, larger: 12}
comparison.checked_theorems
```

The returned `size_monotonicity`, `cost_function_order`, and `budget_order`
are `:checked` after successful Lean verification. The proof scope is
`:cost_functions_budgets_and_executions`. The common verification path audits the
generic theorems and generated certificates; only `propext`,
`Classical.choice`, and `Quot.sound` are permitted as axioms. Existing
integer inference still reports `contract_instantiation: :not_checked`:
this separate comparison does not instantiate or transfer that program's
bound. The conditional execution theorem below is checked separately from
establishing its applicability to a particular target and its callees;
the separate transfer API supplies that connection under explicit conditions.

Auxiliary callee cost names can be included when their parameter
registries match. This checks their mathematical cost items, not the
values or actual costs of external callees. Execution comparison requires
the explicit callee assumptions described below. A name such as `:jit`
still supplies no implementation evidence. The comparison result reports
`execution_cost_order: :checked` for the conditional generic theorem,
`execution_applicability: :not_checked`, `callee_correspondence: :assumed`,
and both `bound_transfer` and `runtime_correspondence` as `:not_checked`.

The Lean theorems apply to the serialized expression and budget syntax.
Elixir declaration validation, metadata compatibility checks, and faithful
serialization remain trusted. The checked budget examples do not prove
universal correctness of the Elixir evaluator or a runtime implementation.

Run the tests with:

```sh
mix test test/reduction_bounds/cost_contract_test.exs \
  test/reduction_bounds/contract_comparison_test.exs
```

Positive cases cover all certificate rules, multiplication, auxiliary
costs, and sequential and alternative budgets. Rejection cases cover
reverse ordering, sampled-but-not-universal inequalities, unsupported
true comparisons, incompatible metadata, symbolic functions, and invalid
budgets. Negative Lean tests alter functions, certificates, and computed
budget values and require rejection.

### Execution-cost comparison under two contracts

`BoundTransfer.lean` reuses `IntegerCost.Runs`; it introduces no new
execution semantics. `compareExecution` takes a finite execution under
charges A and constructs an execution of the same expression, program,
and input environment under charges B. The constructed execution has
the same returned integer, selects the same branches, and has cost at
least the original cost. The operation charges must satisfy
`ChargesLe A B` at every pair of natural parameters. This is separate
from size monotonicity within one charge assignment.

For external calls, `ExternalAgreement admitted externalA externalB`
requires two properties at every admitted key and actual argument:

- The returned values are equal.
- The actual cost under A is at most the actual cost under B.

These are conditional mathematical assumptions about the external models.
They do not follow from an ordering of their upper budgets. For example,
actual costs 9 and 1 can satisfy budgets 10 and 20 while violating the
required actual-cost ordering. Auxiliary cost-expression names also do
not establish value agreement of the corresponding functions.

`CallsWithin admitted run` requires the actual argument of every call
in that execution to satisfy `admitted`. It includes calls inside
argument expressions, bindings, the selected branch, and recursive
bodies. For a call-free execution, the predicate can be false for every
key and argument. No assumption about unused calls is needed.

Induction on this coverage evidence handles every `Runs` constructor:
literals and variables use charge ordering; bindings and arithmetic add
the component inequalities; branches preserve the Boolean test and add
its charge; calls use both external assumptions; recursion combines the
counter, accumulator, and finite body execution. The proof does not
require a uniform charge or restrict integer magnitudes.

`runsDeterministic` proves value and cost uniqueness for a fixed charge
assignment and external model. `executionCostLe` combines this with the
constructed execution, showing that any supplied larger-contract execution
of the same expression and environment returns the same value and has
at least the smaller-contract cost.

`derivationCallsWithin` connects coverage to the existing `Derives`
relation. Under its input coverage, size monotonicity, and
`ContractsHold` assumptions, `derivationSound` supplies the intermediate
value bounds needed to establish each callee's input precondition.
`compareUnderContracts` uses that evidence, including inside finite
recursion, with external agreement restricted to those input contracts.
It does not assume that an initial input condition covers every call
without proving the intermediate conditions.

The comparison API now generates and audits `executionCostOrdering` and
`executionOrderingUnderContracts` for its two concrete mathematical
charge assignments, as well as the five generic comparison theorems.
The result records the following conditions in `execution_conditions`:

- `same_program_and_input`
- `corresponding_charge_events`
- `admitted_call_arguments`
- `callee_value_agreement`
- `callee_actual_cost_order`
- `finite_execution`

`execution_cost_order: :checked` describes this conditional theorem.
The API takes no target program and no callee-correspondence evidence;
therefore `execution_applicability: :not_checked` and
`callee_correspondence: :assumed` remain explicit. It does not report a
successful transfer of a target's bound. The transfer API below rechecks a selected target and requires an explicit
choice of callee correspondence.

The construction transports an already finite normally returning
execution. It supplies no independent claim that an arbitrary recursive
program terminates. The existing finite-derivation termination theorem
and its callee assumptions are retained by the bound-transfer API below.
Exceptions, divergence, concurrency, VM execution modes, and runtime
reduction accounting are outside this comparison semantics.

Reproduce the checks with:

```sh
mix test test/reduction_bounds/contract_comparison_test.exs \
  test/reduction_bounds/execution_comparison_test.exs
```

Positive examples cover bindings, arithmetic, shifts, both Boolean paths,
static calls with different costs, finite recursion, and coverage from a
checked size derivation. A test with distinct charges checks all 13
numeric operation indexes. Rejection examples cover changed returned
values, reversed actual callee costs despite ordered budgets, and a call
outside its admitted argument domain. All generic and generated theorems
are included in the existing axiom audit.

### Transferring a checked integer upper bound

`ReductionBounds.transfer_integer_bound(bound, destination, options)` transfers
an integer bound from its recorded source operation-cost contract B to a
smaller contract A. Both contracts need concrete declarative functions and
the same cost unit, modeled semantics, event profile, parameter meanings,
and all-natural parameter domain. The comparison direction is A ≤ B;
the reused budget is evaluated under B.

The API extracts the target's Core Erlang again from the supplied BEAM or
code path. It reconstructs the input conditions, recursive invariant, and
callee contracts, and repeats bound inference. The stored program, Core
representation, translation certificate, derivation, formula, result size,
and conditions must match the fresh result. Reused callee bounds undergo
the same check recursively. A changed target, altered certificate or formula,
or invalid call contract produces an error. Fields such as `reports` and
`checked_theorems` are not trusted evidence and are not required for replay.
The analysis limits and BEAM binaries can be supplied again for this run.

Lean then checks the original derivation and source correspondence inside
`SourceBound`, and the contract-ordering certificate inside `Comparison`.
Both generators use the same operation registry, including auxiliary cost
names. `sourceContractBound` instantiates the original symbolic theorem
with the concrete B charges. `transferBudgetIdentity` checks that its
budget is the same budget evaluated by the comparison proof. The source
proof and comparison proof are rechecked in the same verification run.

The generic `compareFromLarger` theorem constructs a same-value execution
under A from an execution under B whose calls are covered. Coverage for B
comes from `derivationCallsWithin`, using the source derivation, input
coverage, and source callee contracts. `transferDerivedBound` first
constructs a normally returning B execution with `derivationTerminates`,
then constructs its A counterpart. Determinism identifies that counterpart
with any supplied A execution. Finally, `derivationSound` bounds the B
execution. The theorem and its target specialization `transferredCostChain`
exhibit the source execution and prove

```text
value_A = value_B
C_A ≤ C_B ≤ budget_B
```

Only the B callee budgets are assumed. In particular, a smaller auxiliary
budget need not cover the actual A callee cost. `transferBudget` projects
the result size and upper-bound inequality. `transferredExecutionBound`
specializes it to the rechecked target; `transferredNumericBound` checks
the numeric budget evaluated under B. `transferredSourceBound` connects
the result to the extracted Core evaluation through
`SourceBound.integerCostValueAgreement`.

By default, transfer retains the original input domains. The optional
`input_sizes` can narrow them. An Elixir inclusion check rejects insufficient
input conditions, and `transferInputCoverage` rechecks the inclusion in
Lean. The source recursive invariant and callee contracts are retained.
The contract comparison is universal over natural sizes, so it needs no
additional restricted-domain coverage argument.

For a call-free target, the API can use any shared external model without
additional call conditions. When callee contracts are present, callers must
choose one of the following explicitly:

- `callee_correspondence: :shared` uses the same mathematical external
  value-and-cost model for A and B. Value agreement and actual-cost ordering
  are reflexive, and the B callee contracts remain theorem assumptions.
- A `Lynx.Lean` block defines `transferExternalA`, `transferExternalB`, and
  proves `transferCalleeAgreement`. The agreement predicate is restricted
  to the input domains of `SourceBound.costContracts`. The block must prove
  equal returned values and ordered actual costs; budget ordering alone
  cannot replace this evidence. The generated `transferCallees` theorem
  checks its type and includes its dependencies in the axiom audit.

Missing correspondence is reported as `unresolved_callee_correspondence`.
False proofs and additional axioms are rejected by Lean and the existing
audit. A custom external model is mathematical evidence, not a validation
of an ERTS execution mode or of an actual native callee implementation.
Source callee output and budget assumptions remain explicit even when the
external agreement is proved.

```elixir
alias ReductionBounds.{CostContract, IntegerSize}
functions_b = Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
functions_a = Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
{:ok, b} = CostContract.new(id: :source, functions: functions_b)
{:ok, a} = CostContract.new(id: :destination, functions: functions_a)

{:ok, bound} =
  ReductionBounds.infer_integer_cost_bound({MyModule, :square, 1},
    input_sizes: [%IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}],
    cost_contract: b
  )

{:ok, transferred} = ReductionBounds.transfer_integer_bound(bound, a)
transferred.upper_bound_contract
#=> :source
transferred.upper_bound_value
transferred.checked_theorems
```

`upper_bound` retains the symbolic formula; `upper_bound_contract` identifies
B and `upper_bound_value` records its checked numeric evaluation under B.
Evaluating that formula under A can give a smaller number, but this API
does not claim that number as the transferred bound. The result records
`bound_transfer: :checked`, `source_bound_rechecked: true`,
`comparison_rechecked: true`, and `contract_instantiation: :checked` only
after verification succeeds. The nested original integer result continues
to describe its original parametric proof; these new statuses describe
the transfer proof. Source call assumptions appear in `conditions`, and
`runtime_correspondence` remains `:not_checked` and an unresolved obligation.

`transferTerminates` and `transferredTotal` also construct a normally
returning destination execution. They use the finite source derivation,
input coverage, normally returning source external models under their
contracts, and the callee correspondence. They supply no unconditional
termination guarantee for unsupported recursion or arbitrary callees.
The guarantee is still about the mathematical Core fragment, with the
existing trusted extraction and serialization boundary.

Run the transfer and earlier comparison tests with:

```sh
mix test test/reduction_bounds/contract_comparison_test.exs \
  test/reduction_bounds/execution_comparison_test.exs \
  test/reduction_bounds/bound_transfer_test.exs
```

The transfer tests use arithmetic, branch selection, CRC expressions,
finite sums, a recursive CRC with an invariant, and contracted calls from
the existing integer fixtures. They cover narrower inputs, shared and
proved external correspondences, and reused callee bounds. Rejection cases
cover reverse ordering, incompatible units, symbolic functions, wider
inputs, missing callee correspondence, changed BEAM code, altered bound
evidence, false callee proofs, forged comparison certificates, false
numeric results, and asserted additional axioms.

### Public API integration and evaluation

Successful `compare_cost_contracts/3` and `transfer_integer_bound/3` calls
now include `verification_scope`. The public verification path adds this
summary only after Lean verification succeeds. It does not replace the
proof or accept a caller's status flags as evidence.

| Field | Meaning |
| --- | --- |
| `kind` | The modeled proof scope, matching `proof_scope` |
| `contracts` | `smaller`/`larger` for comparison, or `from`/`to` for transfer |
| `checked` | Completed workflow checks under the stated conditions |
| `assumptions` | Required input and external-call conditions |
| `trusted` | Processing outside the Lean theorem, including metadata checks and serialization |
| `unverified` | Claims outside this proof, including runtime correspondence and wall-clock timing |

Comparison's execution theorem still requires the same program, inputs,
charge events, call-domain coverage, and callee agreement. It selects no
target. Transfer records its actual input domains, recursive invariant,
source callee contracts, and shared or proved external relation. Replaying
source evidence includes Elixir checks followed by Lean proof checking;
it is not a theorem proving the Elixir implementation correct. The trusted
extraction and reification boundary remains explicit. `checked_theorems`
contains the exact audited declarations rather than a list of intended checks.

The APIs preserve their existing error tuples for failed comparisons,
insufficient conditions, and failed Lean proofs. Unknown options in these
two APIs now identify the rejected keys. Comparison accepts only `budget`,
`max_concurrency`, `timeout`, and `lean_options`; `beam_binaries` is a transfer
and source-analysis option, not an input to target-free comparison.

| Diagnostic | Interpretation |
| --- | --- |
| `unknown_options` | One or more option names are not accepted by this API |
| `invalid_option` | An accepted option has an invalid value |
| `invalid_cost_contract` | The indicated declaration or profile is unsupported |
| `incompatible_cost_contracts` | Units or parameter meanings do not match |
| `unresolved_cost_functions` | A required concrete function remains symbolic |
| `unresolved_cost_order` | The structural search did not prove the required direction |
| `missing_call_contract` | A static callee lacks a contract; reported within `integer_cost_source` |
| `call_precondition` | Inferred arguments do not establish a callee's input conditions; reported within `integer_cost` |
| `insufficient_transfer_inputs` | Destination input conditions do not establish the source precondition |
| `unresolved_callee_correspondence` | The transfer needs an explicit shared model or a Lean correspondence proof |
| `original_bound_mismatch` | Replayed source evidence differs from the supplied bound |
| `verification_failed` | Lean rejected the generated proof or its axiom dependencies |

In comparison diagnostics, `smaller` denotes A and `larger` denotes B.
In transfer, A is the destination and B is the source. Units and semantic
labels alone never authorize a comparison or transfer. An unresolved true
inequality is reported conservatively, not classified as false.

`ContractWorkflowTest` exercises the public APIs using the existing integer
fixtures under distinct nondecreasing polynomial charge functions. Each
positive case derives a source bound, checks contract ordering, transfers
the bound, and checks the returned scope and source-budget value.

| Evaluation | Existing fixture | Reused checks |
| --- | --- | --- |
| Arithmetic and bindings | `product/1` | Integer size derivation and source correspondence |
| Branch selection | `guarded/1` | Branch refinement and maximum budget |
| Finite recursion | `sum/2` | Finite derivation and conditional termination |
| Variance arithmetic | `variance_numerator/3` | Multiple input sizes, products, and subtraction |
| CRC update | `crc64_update/2` | Intermediate widths, shift, XOR, and masking |
| Reflected CRC index | `crc64_reflected_index/2` | Wide inputs, masking, and addition |
| Contracted call | `caller/1` and `helper/1` | Rechecked callee bound and explicit shared external model |

Rejection checks in this evaluation cover public option validation,
unsupported profiles and registries, incompatible units, reverse ordering,
symbolic functions, missing callee contracts, insufficient call inputs,
and missing external correspondence. The earlier comparison, execution,
and transfer test modules additionally cover sampled-but-not-universal
inequalities, forged evidence and axioms, wider transfer inputs, changed
BEAM code, and false callee value or actual-cost correspondence.

From the project root with its pinned Lean toolchain installed, run:

```sh
mix test --only cost_contract_workflow --trace
```

To print each case's formula, source-contract numeric bound, input conditions,
verification scope, and audited theorem names:

```sh
REDUCTION_BOUNDS_REPORT=1 mix test --only cost_contract_workflow --trace
```

The proposed Issue #2 criteria can be checked against the following evidence:

| Acceptance criterion | Reproduction evidence |
| --- | --- |
| Identify cost contracts and their applicability conditions | `cost_contract_test.exs`, integer analysis results, and `verification_scope.assumptions` |
| Check an ordering between contracts in Lean | `contract_comparison_test.exs`, `execution_comparison_test.exs`, and audited comparison theorems |
| Transfer a verified bound between contracts | `bound_transfer_test.exs` and `transferredCostChain` |
| Report unsupported comparisons and unresolved obligations | Public workflow rejection cases, existing transfer rejection cases, and `verification_scope.unverified` |
| Provide reproducible positive and rejection tests | The tagged public workflow and the full comparison and transfer test modules |
| Keep concrete execution-mode correspondence explicit | `runtime_correspondence: :not_checked` and the reported runtime and timing exclusions |

The report is generated from successful results at test execution time.
No fixed test count or precomputed numeric outcome is treated as evidence.
This is a symbolic verification evaluation, not a measurement of ERTS
reductions or processor time. For full project validation, run:

```sh
mix check
mix test
mix docs
```

### Size-dependent charges and composition

A cost leaf `{:cost, name, [a, b]}` denotes `charge(name, a, b)`.
The mathematical contract requires a natural-valued cost function
nondecreasing in both size parameters. The arithmetic and XOR leaves
use magnitude bounds for their operands. A shift leaf uses the input
magnitude bound and constant shift amount. A mask leaf uses the input
magnitude bound and constant mask width. Value evaluation, variable
lookup, binding, and the local static- and recursive-call charges use parameters
`[0, 0]`. A comparison charge includes the variable and constant used
in the branch test; their retrieval is included in that local charge.
Unary signs are lowered to addition or subtraction from zero, including
the corresponding zero-literal charge in this conservative cost model.

`Budget` in `IntegerCost.lean` combines leaves by addition for sequential
work and maximum for alternatives. If an actual operand has magnitude
`beta(v)` and its inferred bound is `w`, `knownWidth` supplies
`beta(v) <= w`. `MonotoneCharges` then justifies replacing the actual
size by `w` in the charge. The proof reuses the existing `IntegerSize`
arithmetic, shift, mask, refinement, and join theorems.

`Derives` records the derivation for literals, variables, bindings,
operations, branches, static unary calls, and two-argument self calls.
Every intermediate summary is explicitly typed in the generated
certificate, so a changed intermediate size or budget must also pass
the rules. `derivationSound` proves, for every modeled execution under
its input conditions and call contracts, both result-size membership
and the cost inequality. `derivationTerminates` constructs a finite
normally returning execution from a finite checked derivation. External
functions denote normally returning mathematical call models; their
contracts are explicit assumptions about their results and costs.

### Static call contracts and checked callee reuse

Local and remote unary calls use the same contracts. A `call_contracts`
map is keyed by `{module, function, 1}`. A supplied
contract contains `input_size`, `result_size`, and `upper_bound`. The
call argument is analyzed first. `included/2` checks that its domain
is contained in the required input domain; `inclusionSound` proves the
semantic inclusion. The result description then propagates into the
caller, and the callee budget and local static-call charge are added to
the argument-evaluation budget.
Unknown result widths remain visible in `unresolved_sizes`; attempting
to use such a value at a size-dependent operation reports an error.

A unary result returned by `infer_integer_cost_bound/2` can itself be
supplied as a contract. Its source and cost certificates are regenerated
and checked in a separate Lean namespace in the caller's verification.
`costReuseN` checks equality of the reused output description and budget
with the callee summary. The same symbolic cost-function registry is
used across the proofs. Nested checked contracts are rechecked recursively.
The axiom audit includes the reused proofs, not just their names in
an Elixir result map. A user-supplied contract is recorded as
`:user_contract`; a rechecked result as `:checked_model_bound`.

Call-model agreement remains an explicit assumption even for a
rechecked callee bound: a bound proved for a model does not by itself
identify an arbitrary external function with that model. No contract
is silently inferred for an unsupported call, BIF, or NIF. This phase
does not establish native-code behavior, yielding, or ERTS accounting.

### Finite recursion and invariant preservation

For two-argument self recursion, the analyzer propagates the two
argument domains into another copy of the same body. Every reachable
branch needs a complete derivation. `max_unfolding` limits nested self
calls and `max_nodes` limits analysis nodes. If a live recursive path
still requires expansion at the limit, the result is
`:unresolved_recursion`, not a successful result conditional on assumed
termination. These limits control analysis effort. They are not input
preconditions or execution bounds.

With a finite counter range, this permits a sequence of different
operand-size bounds. For example, `sum(counter, accumulator)` adds the
positive counter and calls itself with its predecessor, returning the
accumulator otherwise. From counter range `[0, 4]` with magnitude bound
3 and initial accumulator zero, the result interval is `[0, 10]`,
with a conservative propagated magnitude bound of 7. The budget adds
size-dependent costs at each expanded level and takes maxima over the
possible stopping branches. There is no assumption that the initial
accumulator width bounds all later additions.

An optional two-element `recursive_invariant` supplies independent
integer domains for the counter and accumulator. The analyzer checks
inclusion at entry and at every reachable self call. More importantly,
the `Derives.recur` constructor requires a semantic invariant proof
for every pair of values admitted by that call's argument summaries.
`derivationInvariant` proves `RunInvariant` for every modeled run:
the supplied invariant holds at every recursive call, including those
inside bindings and branches. `integerCostInvariant` instantiates
this theorem. `costInvariants` also checks the recorded domain-inclusion
obligations. Automatically inferred domains and the supplied invariant
are separately exposed in `conditions`.

The CRC loop fixture uses counter interval `[0, 4]` without a magnitude
constraint in the invariant, and accumulator interval `[0, 255]` with
magnitude bound 8. Its initial counter description still supplies a
magnitude bound for cost inference. Each update shifts and applies XOR
before masking. The intermediate widths remain in the derivation,
while the mask reestablishes the eight-bit accumulator invariant.
An invariant requiring an unchanged zero accumulator for the sum
fixture is rejected. This domain does not represent relational
invariants between the counter and accumulator, and this implementation
does not synthesize closed recurrences with an unbounded symbolic
counter. It verifies each supplied finite input range by a finite
derivation.

### Reified Core semantics and transformation checking

`IntegerCostSource.lean` defines an annotation-free Core fragment with
integer literals, variables, single-variable lets, calls with retained
module/function atom spellings, two Boolean case clauses in their
original order, local unary calls, and two-argument local self calls. The Elixir reifier
rejects unsupported constructors and guards. The supported tests compare
a variable with an integer constant, on either side. Comparison of two
arbitrary expressions is outside this entry point's current profile.
Native arithmetic, shifts, masks, and comparison semantics are
mathematical integer models, without runtime representation boundaries.

`Translates` is a checked lowering relation. Its premises check the
actual operation names, constant amounts, low-bit masks, Boolean clause
order, variable indices, and self-call name. A registered external call
must have the matching module and function. `UniqueNames` rules out
ambiguous external registrations. `sourceAgreement` maps every costed
model execution to a source execution with the same value.
`sourceComplete` maps every execution of the reified source fragment
back to a costed model execution. This includes recursive body calls.

For each target, `integerCostValueAgreement` states the resulting
value equivalence. `integerCostSourceBound` connects every source result
to a costed run satisfying the result description and budget.
`integerCostSound` bounds every model run. `integerCostTotal` constructs
a finite source and model execution under the stated input and call
conditions. `costCandidate` checks the returned result description and
budget, and the common verification path audits the dependencies of
these theorems and any reused proofs. Only `propext`, `Classical.choice`,
and `Quot.sound` are permitted as axioms.

The remaining trusted boundary is extraction and faithful reification
of the accepted Core syntax, plus the choice of mathematical primitive
semantics. This is not a formalization of the entire Erlang language,
a compiler-correctness theorem, or a proof about arbitrary BEAM bytecode.
The result reports `proof_scope: :reified_core_integer_cost_fragment`,
`value_agreement: :checked`, and `runtime_correspondence: :not_checked`.
Neither this result nor its termination theorem identifies symbolic
costs with ERTS reductions or elapsed time.

### Reproducing the integer cost cases

The module documentation gives examples of a recursive sum, a checked
callee reused by its caller, a supplied external call contract, and
a recursive accumulator invariant. The fixture
`test/fixtures/integer_cost_programs.ex` supplies compiled arithmetic,
branching, CRC, caller, and recursion cases. Run:

```sh
ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)" mix test \
  test/reduction_bounds/integer_cost_bound_test.exs
```

The tests check the reported formulas, size information, conditions,
and theorem names, compare returned values with the compiled fixtures,
and exercise missing widths, missing or inapplicable call contracts,
invalid invariants, endless recursion, and analysis limits. Negative
Lean tests change a result, budget, source operation, or intermediate
summary and require rejection. A falsified callee result must also be
rejected when supplied to a caller.

### Signed boundaries, cancellation, and wide intermediates

The Issue #1 boundary regressions use mathematical magnitude boundaries,
not a fixed small-integer/bignum representation threshold. For widths
1, 8, 32, 64, and 200, the domain tests cover both signs immediately
below, at, and above `2^width`. They check exact constant descriptions,
the strict magnitude condition, and carry and negative subtraction
results. The Lean comparison test checks the same signed boundary
family against `Holds` and `contains`.

The compiled cost fixtures exercise addition and subtraction around
signed boundaries at widths 1, 32, 64, and 200. Their tests require the
source-bound theorem and retain the operand widths in the cost leaves.
They also compare the compiled functions' endpoint results with the
inferred result descriptions.

`cancel_products/2` squares two independently supplied signed inputs
and subtracts the products. For inputs `-(2^200 + 1)` and `2^200 + 1`,
the final result is zero. The trace must nevertheless retain both
products with magnitude bound 402, both multiplication charges with
operand bounds `[201, 201]`, and the subtraction charge with operand
bounds `[402, 402]`. This prevents a small final result from hiding
large intermediate work. A negative Lean test changes the returned
budget to charge those multiplications at zero operand width and
requires rejection.

`crc64_step/1` is a CRC-style expression with a fixed polynomial and
a 64-bit mask, not a complete CRC implementation. On input interval
`[-2^64, 2^64]` with magnitude bound 65, shifting left by eight gives
bound 73 and signed XOR gives conservative bound 74. The mask returns
range `[0, 2^64 - 1]` with magnitude bound 64. The test requires the
shift, XOR, and mask cost leaves to use their respective intermediate
operand sizes, including the 74-bit input to the mask. It checks
compiled results on negative, zero, and positive boundary inputs.

Reproduce these regressions with the existing integer test files:

```sh
ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)" mix test \
  test/reduction_bounds/integer_size_test.exs \
  test/reduction_bounds/integer_size_proof_test.exs \
  test/reduction_bounds/integer_cost_bound_test.exs
```

These cases cover the VM-independent portion of acceptance criterion 2:
signed size boundaries, negative values, cancellation, and integers much
wider than a machine word. The finite comparisons supplement the generic
Lean theorems; they do not prove correctness of the Elixir compiler or
runtime arithmetic. The tests keep `runtime_correspondence: :not_checked`.
They do not detect native integer representations, establish a
small-integer/bignum transition threshold, measure ERTS reductions, or
claim conformance with a complete CRC-64 algorithm. Representation
boundary tests remain a separate implementation-specific validation task.

### Representative variance and table-driven CRC expressions

The acceptance criterion about representative variance and CRC
expressions is exercised in
`test/reduction_bounds/integer_cost_cases_test.exs`, using the compiled
fixture `test/fixtures/integer_cost_cases.ex`. These kernels use the
existing integer size and cost rules; there is no new recognizer or
cost rule specific to variance or CRC.

The variance kernels follow the integer expression in the
[Mobius change motivating Issue #1](https://github.com/mobius-home/mobius/commit/bf00f21638b12bf9a3a683126dc5a1cf87f58983).
For a count `n`, sum `s`, and sum of squares `q`, the numerator is
`n * q - s * s`, and the denominator is `n * (n - 1)`. The numerator
takes three integer arguments; the denominator's test requires
`2 <= n <= 8`. Division, floating-point conversion, clamping, and square
root are outside these kernels and have no supplied contracts here.
The fixture does not analyze the complete Mobius module.

The exact-input tests use closely spaced positive and negative samples
near `1_788_878_897_448`, samples near `2^200`, and identical samples
near `2^200`. The compiled numerator returns 6 or 0 while both products
exceed `2^64`. The tests compare it with the independent identity
`sum((x_i - x_j)^2, i < j)`, check the exact result interval, and retain
both product summaries and size-dependent multiplication charges.
A negative Lean test requires rejection of a zero budget for this work.
An interval-input test also checks the bound on independently specified
summary ranges and compares the compiled expression on a finite grid
of three-sample datasets. Statistical consistency of arbitrary summaries
is not assumed: independent intervals can include combinations that
are not summaries of any dataset. Consequently, that interval analysis
does not establish that every admitted numerator is nonnegative.

The CRC kernels follow the table-driven expressions in
[the cerlc implementation](https://github.com/mdsebald/cerlc/blob/750d85e56ecef4770583f495faace160398b195d/src/cerlc.erl),
specialized to a 64-bit state. Let `u` be the current state, `t` a table
entry, and `b` an input byte. Their arithmetic is:

| Kernel | Integer expression |
| --- | --- |
| Normal update | `((u << 8) XOR t) AND (2^64 - 1)` |
| Reflected update | `((u >> 8) XOR t) AND (2^64 - 1)` |
| Normal table index | `(((u >> 56) XOR b) AND 255) + 1` |
| Reflected table index | `((u XOR b) AND 255) + 1` |

The update contracts require both inputs in `[0, 2^64 - 1]`, with
magnitude bound 64. The normal path records a 72-bit shift bound and
a conservative 73-bit XOR bound before masking to 64 bits. The reflected
path retains the conservative 64-bit right-shift bound, then a 65-bit
XOR bound before masking. The mask's charge uses the intermediate
width, not the final width. Index inputs require a 64-bit state and
byte range `[0, 255]`; the resulting one-based index is in `[1, 256]`.
Tests cover all 256 byte values for selected boundary states.

These are arithmetic expressions, not a full CRC implementation. The
table entry is an explicit input with a stated size condition. Table
lookup, table generation, records, byte-list traversal, configuration,
and final XOR are not analyzed by these cases. No claim is made that
an arbitrary supplied table implements a particular CRC polynomial.

For every successful case, the test requires checked source agreement,
the source cost-bound and totality theorem names, no unresolved sizes,
and no external call contracts. The result remains
`runtime_correspondence: :not_checked`. The generic Lean theorems cover
the reified supported kernels under their input and symbolic-cost
conditions; comparisons with compiled fixtures are finite regression
checks, not compiler or ERTS correctness proofs.

Run the representative-expression cases with:

```sh
ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)" mix test \
  test/reduction_bounds/integer_cost_cases_test.exs
```

## Shared communication events, traces, and contracts

`ReductionBounds.Protocol` defines finite protocol contracts shared by the
Port and request/response work. Contracts declare participants and their cost
units, states, an initial state, terminal states, event ownership, and allowed
transitions. A work event belongs to exactly one participant and carries that
participant's unit. An environment observation has neither an owner nor a
cost unit. In particular, observing an arrival does not bound external work.
Different participants may use different units; this layer does not sum them.

`ReductionBounds.Protocol.new/1` validates declarations. It rejects unknown states or events,
ambiguous transitions for the same state and event name, transitions leaving
terminal states, and inconsistent ownership or units. `ReductionBounds.Protocol.check_trace/2`
checks supplied event occurrences and records all visited states. Empty traces
and unfinished prefixes are accepted when admissible. Invalid occurrences
report a zero-based index, the event, and the reason. `terminal?` classifies
the end of this supplied trace, not a guarantee that all interactions finish.
`ReductionBounds.Protocol.events_for/2` selects occurrences owned by a participant.

The initial `ReductionBounds.PortProtocol` model assumes that the caller is
the Port owner and at most one request is in progress. Preparation is followed
by acceptance, rejection, or submission suspension. Rejection can be returned
or retried. Suspension handling and resumption are explicit work events;
waiting itself is a state. After acceptance, an environment response-arrival
event precedes caller-side retrieval and decoding. Closure is another
environment observation; a distinct caller-owned event handles the closure
before reaching the closed terminal state. A second submission after acceptance, duplicate
arrival, or response retrieval before arrival is rejected by the model.

```elixir
alias ReductionBounds.{PortProtocol, Protocol}
{:ok, contract} = PortProtocol.new()
names = [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode]
events = Enum.map(names, fn name ->
  {:ok, event} = Protocol.event(contract, name)
  event
end)
{:ok, trace} = Protocol.check_trace(contract, events)
{trace.final, trace.terminal?}
#=> {:complete, true}
Enum.map(Protocol.events_for(trace, :caller), & &1.name)
#=> [:prepare, :submit_accepted, :receive_response, :decode]
```

`ProtocolProof.build/2` rechecks the supplied model trace and generates Lean
contract, event, and successor-state declarations. `ProofInput.protocol_postludes/1`
loads `priv/lean/reduction_bounds/Protocol.lean`. Its `checkTraceSound` theorem
proves that an accepted certificate describes a `Runs` derivation of allowed
transitions under a well-formed contract. The successor-state list is checked
by Lean rather than trusted. `Runs.eventsValid` establishes registration and
accounting metadata for every occurrence. `ownerExclusive` prevents one
occurrence from having two different owners. `Runs.preserves` transports an
arbitrary state invariant from the initial to final state when each allowed
step preserves it; such step obligations remain explicit. The generated
`suppliedInvariant` specializes this rule to the supplied trace. Selected
shared and generated theorem dependencies are audited against the existing
axiom allowlist, including rejection of unfinished proof replacements.

Reproduce both the Elixir validation and Lynx/Lean checks with:

```sh
mix test --only protocol_model
```

Tests cover success, rejection, retry, closure, suspension and resumption,
waiting prefixes, event ownership and units, malformed declarations, and
illegal transitions. Altered successor states and event ownership are rejected
independently in Lean, even if the generated certificate text is modified.

This shared trace layer alone supplies no cost functions or size and
event-count bounds. The checks below add explicit conditions to that layer. Retry and receive-inspection cycles
may occur arbitrarily often in that unrestricted trace layer. The cost-safety
and conditional-completion sections below add separate bounds and progress
hypotheses. Neither layer connects a target Core Erlang function to the
protocol or covers a real Port program or driver. Faithful serialization and the chosen
protocol remain trusted. Port-side and external-computation costs, concrete
ERTS charging, runtime timing, and scheduler behavior remain unverified.

## Communication size and event-count conditions

`ProtocolSize` describes independent byte and structural upper bounds. Unknown
fields are `:unknown`, never zero. `ProtocolSize.from_iodata/1` counts one
structural unit for every binary, byte, empty list, and list cell. Thus
`[[], []]` has zero bytes and five structural units, whereas a 1000-byte binary
has 1000 bytes and one structural unit. Binary traversal still needs its byte
bound. Valid binary tails are supported; scalar top-level bytes, non-byte list
items, non-binary improper tails, and bitstrings with fractional bytes are
rejected. This measure does not specify ERTS allocation or reduction charging.

`ProtocolConditions` adds a condition profile to a supplied protocol contract.
Every allowed state/event context must have an explicit `Rule`, even an empty
one. Rules name data requirements, integer requirements, and counters. Data
bounds require both dimensions to be finite. Integer bounds reuse
`IntegerSize` value ranges and magnitude bounds, with a finite magnitude bound
and a nonempty domain. Data and count declarations are validated even for
branches not visited by a supplied trace. No request-to-response size relation
or integer-to-byte encoding relation is assumed or synthesized.

`PortProtocol.conditions/1` supplies rules for the initial Port model. Its
independent data fields are `:request`, `:response`, and `:message`; the last
covers inspections of messages that do not match. Matching response retrieval uses the
response bound and also increments `:receive_inspections`. The profile requires
finite caps for `:total_events`, `:submission_attempts`, `:submission_events`,
`:resumptions`, `:retries`, and `:receive_inspections`. Total events include
work and environment observations. All other counters count named occurrences
across the entire trace, including repeated scans and events after arrivals.

The Port model now distinguishes `:submission_resumed` from `:prepared`.
Starting submission from `:prepared` increments the attempt count. After a
suspension, a resumed outcome increments the submission-event count without
starting another attempt. Repeated suspension/resumption still contributes
work events and is limited independently. This prevents a single suspended
submission from being counted as multiple new attempts.

```elixir
alias ReductionBounds.{PortProtocol, Protocol, ProtocolConditions, ProtocolSize}
{:ok, profile} = PortProtocol.conditions(
  data_bounds: %{
    request: %ProtocolSize{bytes: 8, structure: 10},
    response: %ProtocolSize{bytes: 4, structure: 8},
    message: %ProtocolSize{bytes: 8, structure: 8}
  },
  count_bounds: %{total_events: 10, submission_attempts: 1,
    submission_events: 1, resumptions: 0, retries: 0, receive_inspections: 1})
names = [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode]
events = Enum.map(names, fn name ->
  {:ok, event} = Protocol.event(profile.contract, name)
  event
end)
{:ok, observation} = ProtocolConditions.observe(%{request: [1], response: <<2>>, message: []})
observations = events |> Enum.with_index() |> Map.new(fn {_event, i} -> {i, observation} end)
{:ok, result} = ProtocolConditions.check_trace(profile, events, observations)
result.counts
#=> %{total_events: 5, submission_attempts: 1, submission_events: 1,
#=>   resumptions: 0, retries: 0, receive_inspections: 1}
```

Optional `integer_events` associates event names with integer-condition names
in `integer_bounds`. `ProtocolConditions.observe/2` accepts a separate map of
mathematical integer values. The checker uses `IntegerSize.contains?/2`; a
large integer cannot be substituted directly for an encoded iodata byte.
Custom state-specific conditions can be declared through
`ProtocolConditions.new/2`. Results retain the supplied profile and the
per-occurrence state, rule, observation, and independently computed counters.
Missing bounds, missing observations, unknown dimensions, exceeded caps, and
invalid observation indexes are errors. A zero-length prefix has zero counts
but does not imply completion.

`ProtocolConditionsProof.build/3` rechecks the trace and emits the profile,
observations, and reported counts. `ProofInput.protocol_condition_postludes/1`
loads the integer-size semantics and the shared protocol and condition rules.
Lean's `checkConditionsSound` connects the accepted certificate to the shared
`Runs` relation, well-formed declarations, `RowsHold` for every occurrence,
and `CountsHold` for every declared counter. `RowsHold` requires both data
inequalities and the existing `IntegerSize.Holds` proposition. `countFrom`
recomputes counts from the Lean events, states, and rules rather than trusting
an Elixir total. Generated theorems additionally check that reported count
names and values match that computation. Selected dependencies are audited.

Reproduce the new cases with:

```sh
mix test --only protocol_conditions
```

Tests cover independent response and structure bounds, nested empty lists,
wide integers, resumed submission accounting, scans across arrivals, matching
inspections, missing conditions, and invalid iodata. Lean independently rejects
altered size summaries, count caps, reported counts, unknown magnitude bounds,
and unfinished condition certificates. The `protocol_model` tests continue to
exercise the underlying trace layer.

These are checks of supplied model traces under explicit conditions, not an
inference of bounds for all possible runs. The Elixir validator returns
`lean_status: :not_checked`; generating proof text also does not execute Lean.
The integration tests perform that separate check through Lynx. Association
of size summaries and integer values with actual target data, Elixir iodata
measurement, and faithful serialization remain trusted. No concrete encoding,
source-code correspondence, cost bound, progress guarantee, or ERTS accounting
is established at this stage. Later all-trace cost proofs must state these
size and count conditions as premises, rather than infer them from one sample.

## Map and struct operations

The decoder handles fixed atom keys and the supported Boolean guard
forms. For a case over multiple input variables, the first pattern must
be a supported map pattern and the other patterns must bind distinct
variables. When a pattern matches and its guard fails, evaluation
continues with the next clause in the original environment. Case tails
outside the supported fragment are retained in the returned
`normalization.program.opaque` map.

For `BoundedCounter.read_checked/1`, the normalizer learns that
`balance` exists from a successful pattern match and carries the fact
through the alias. It replaces the subsequent access case with a field
read. The normalizer leaves `read_unchecked/1` unchanged.

The value check takes its source tree from the Core Erlang recovered
from BEAM debug information. The source tree retains map pattern aliases.
`coreDecoding` checks that the decoder's output equals the result of
lowering that tree in Lean. `SourceExpr.lowerSound` proves that this
lowering preserves evaluation and checks that any alias reads the
original subject before binding its new name.

`coreNormalization` checks the entire rewrite starting with an empty
set of field facts. A successful map match establishes field presence
in its matched branch. A variable binding copies the source's facts
to its new name and removes any facts about the previous binding of
that name. The fallback uses the incoming facts. `coreValueAgreement`
combines the decoding and rewrite checks to prove that the extracted
source tree and the normalized expression evaluate to the same result.
Lean rejects rewriting an unchecked access to a direct field read.

`infer_struct_bound/2` reports `value_agreement: :checked` for successful
checks in this source fragment. Extraction and serialization supply the
tree to Lean. Compiler-generated case tails outside the fragment retain
their identifiers and are interpreted by the same parameter on both
sides of the theorem. For a matched `read_checked/1` input, neither side
uses that parameter. Targets outside this fragment, including the
guarded examples below, report `value_agreement: :unsupported`. Their
available local certificates are checked under their listed assumptions.

The upper bound is computed for the fragment **before normalization**.
`{:operation_cost, kind}` denotes a supplied upper charge for an
operation. `{:opaque_cost, id}` denotes a supplied upper charge for all
work in a retained path, including exceptional exits where applicable.
The result lists those identifiers in `opaque_paths`. Sequential cost
items are added and alternatives are combined with a maximum. The Lean
theorem `CostTree.pathCostBound` applies to every derivable path whose
local costs obey the supplied charges. `structCostBound` checks the
returned formula against the cost tree built in Lean from the decoded
fragment. The tree can include infeasible paths, such as a compiler
fallback for updating a value already known to be a map.

Call `ReductionBounds.infer_struct_bound({module, function, arity})` to
derive a symbolic upper bound for a supported Core Erlang function. For
an in-memory module, pass its compiled binary in `beam_binaries`.
`BoundedCounter.debit/2` exercises tagged map patterns, alias bindings,
short-circuit conjunction, subtraction, and exact field updates.
`BoundedCounter.set_limit/2` uses the same rules with a different field
and guard.

## Execution soundness for unary Core Erlang functions

`ReductionBounds.infer_verified_bound/2` checks an upper bound against
the execution semantics of a unary numeric fragment. The precondition
is a nonnegative integer input. The function dispatches on zero and a
default clause. Its body may evaluate bindings, nested zero tests,
nonnegative integer values, addition, static unary calls, and self
calls on the input minus one.

The Elixir decoder checks the Core Erlang shape extracted from BEAM
debug information and resolves its variable bindings. The Lean
semantics in `ExecutionBound.lean` starts at the reified program.
`Eval` relates an expression to its value and its charged symbolic
cost. It evaluates both parts of a binding in order, evaluates the
test before choosing a branch, and gives each static call any result
and cost permitted by the callee relation. `Program.runs` covers all
finite derivations, indexed by a call depth. The evaluator passes the
actual recursive operand to the next call. A separate checked rule
establishes that the operand denotes the current input minus one and
that a self call occurs only in the positive clause. Rebinding a name
discards its previous predecessor fact.

Each entry in `call_contracts` maps a static callee to its cost limit.
The limit excludes the caller's own call charge. The cost proof assumes
that every callee outcome for a natural argument stays within that
limit. Normal return assumes the callees terminate normally and return
natural results on those arguments. Lean uses a total relation to
construct a terminating derivation by induction on the input.
`targetTerminates` gives a maximum self-call depth of `n + 1`, counting
the initial call, for this construction.

`Eval.pathCost` constructs a derivation for the existing `CostTree`
rules. `targetUpperCorrect` checks the candidate equations generated
in Elixir against the Lean bound. `targetCostBound` then bounds every
execution in `Program.runs` under the call cost contracts. The result
contains the precondition, the contracts used, and the zero and
successor equations. In the successor equation, `:previous` denotes
the upper bound at the preceding input.

The API reports unsupported source expressions, missing callee
contracts, and failed Lean checks as errors. Tests confirm that Lean
rejects a self call on the unchanged argument and a falsified bound.
Source extraction and the decoder's reification are trusted for this
numeric fragment. The specialized list, map, and buffer analyses have
their own proof scopes.

## User-defined list traversals

`ReductionBounds.infer_list_bound/2` recognizes a traversal with an
empty-list clause and nonempty-list clauses. A nonempty clause may
return immediately or call itself once on the tail, passing the same
key when there is one. The analyzer assigns symbolic charges to clause
dispatch, values, integer addition, and recursive calls. It adds the
costs of sequential expressions. A dispatch charge covers the tests
that led to the selected clause, including rejected earlier clauses.

Lean's `ListCost` relation describes the costs of these three cases.
`listRulesSound` bounds every derivation by `base + n * step` when
`n` bounds the list length, `base` bounds the empty and early-stop
charges, and `step` bounds the local cost of a recursive clause. The
proof uses the fact that a recursive clause makes at most one call
and consumes one list cell. `listPathBounds` distinguishes paths that
reach the empty list from paths that stop early. An early stop requires
a remaining cell, so it can follow at most `n - 1` recursive steps.
The result exposes both `upper_bound` and `refined_upper_bound`.

For recognized membership and length functions on proper integer lists,
Lean also checks that the costed model returns the same value as the
Lynx translation. When `value_model` is `nil`, the checked claim is the
cost inequality for the modeled derivations.

`ReductionBounds.infer_search_bound/2` provides a dedicated analysis for
the membership pattern. The function returns false for an empty list,
returns true on an exact match at the head, and otherwise searches the
tail with the same key. Its `searchCostBound` theorem bounds the cost
model by `max(c_empty, c_hit) + n * c_step`, where `c_step` is the
local charge of a miss before continuing. This entry point checks the
cost inequality for that model.

## lists:member/2

Call `ReductionBounds.infer_list_bound({:lists, :member, 2})` to check
the bound for the Erlang built-in. The analysis uses the built-in value
model `Erlang.lists.«member/2»` supplied by Lynx. The inputs in the
theorem are an integer key and a proper list of integers, encoded as
Lynx terms. The size parameter `n` is any natural number at least as
large as the input list length.

### Value agreement

The costed model returns a pair consisting of the Boolean result as a
Lynx atom and a symbolic cost. It returns `false` for an empty list,
returns `true` at the first element exactly equal to the key, and
otherwise continues on the tail. Lean proves by induction on the input
list that the value component agrees with the result of the Lynx model.
In the inductive step, exact comparison of two encoded integers reduces
to equality of their integer values.

### Cost recurrence

The cost theorem holds for every assignment of natural numbers to
the model's charges. Write `E` for the total charge of the empty case,
`H` for the charge of a hit at the current head, and `S` for the local
charge of a miss that continues to the next cell. `S` excludes the cost
of searching the tail. In the returned expression, the
`:recursive_call` charge labels continuation in this model.

| Case | Modeled cost |
| --- | --- |
| Empty list | `E` |
| Head equals the key | `H` |
| Head differs from the key | `S + cost(tail)` |

The theorem `searchCostDerivation` proves that the cost computed by the
model has a derivation in the shared `ListCost` relation. Each
continuation decreases the input length by one.

### Upper bounds

The result contains the following two bounds.

| Result field | Upper bound |
| --- | --- |
| `upper_bound` | `max(E, H) + n * S` |
| `refined_upper_bound` | `E` if `n = 0`, and `max(E + n * S, H + (n - 1) * S)` if `n > 0` |

An exhaustive search can continue at most `n` times and then reach the
empty list. A search that hits must still have a head to inspect,
so it can continue at most `n - 1` times before the hit. When
`n = 0`, only the empty case is possible.

The generated theorem `listValueAndBound` combines value agreement
with both cost inequalities. It is checked by Lean when inference
runs, and the ExUnit case exercises that path through the public API.

## lists:reverse/2

Call `ReductionBounds.infer_list_bound({:lists, :reverse, 2})` to check
the bound for reversal with an accumulator. Both inputs are proper
integer lists. Write `xs` for the first argument and `acc` for the
accumulator. The size parameter `n` bounds the length of `xs`.

### Value agreement

The costed model returns `acc` when `xs` is empty. For a nonempty
list, it prepends the head to `acc` and continues on the tail. Lean
proves by induction on `xs`, with the accumulator generalized, that
the model agrees with Lynx's `Erlang.lists.«reverse/2»` and returns
`xs.reverse ++ acc`. Reversing `[1, 2]` onto `[3, 4]` gives
`[2, 1, 3, 4]`. An empty accumulator gives `[2, 1]`.

### Cost recurrence and upper bound

Let `E` be the symbolic charge for returning the accumulator, and let
`S` be the local charge for moving one head to the accumulator and
continuing. The charges range over the natural numbers.

| Input | Modeled cost |
| --- | --- |
| `[]`, `acc` | `E` |
| `head :: tail`, `acc` | `S + cost(tail, head :: acc)` |

The theorem `reverseCostDerivation` proves that the computed cost has a
derivation in the shared `ListCost` relation. Every step consumes one
cell of the first list. The model reaches the empty case after
`xs.length` steps, so both `upper_bound` and `refined_upper_bound`
are `E + n * S`. The bound has no term for the length of `acc`.

The generated theorem `listValueAndBound` gives the result equation
and both inequalities for all values of `acc` in the stated domain.
When supplied, an `input_contract` constrains `xs` and supplies its
size measure.

## Input contracts and forwarding calls

For a recognized value model, `infer_list_bound/2` accepts a Lean block
as the `input_contract` option. The block defines `inputPrecondition`,
`inputInvariant`, and a natural-valued measure `inputSize` on integer
lists. It proves that the precondition establishes the invariant
(`inputInvariantInit`), that the invariant holds for the tail
(`inputInvariantTail`), and that the measure decreases by at least one
on a tail step (`inputSizeTail`).

`inputLengthBound` then proves `xs.length ≤ inputSize xs` by induction
on the list. The generated theorem `listInputValueAndBound` applies
the model's cost theorem with `inputSize xs` under the precondition
and includes value agreement. For example, a contract can require
`xs.length < 100` and supply `xs.length + 2` as the size measure.

`ReductionBounds.infer_list_call_bound/3` checks that a local wrapper
forwards every argument in the original order to a different function in
the same module. It supports recognized membership, length, and reversal
models. Lean checks the callee theorem in the same run and applies it in
`listCallerValueAndBound`. The wrapper's upper bound is
`caller_cost + callee_refined_bound`. The symbolic `caller_cost` covers
the wrapper's own work. With an input contract, the wrapper proof uses
the same precondition and size measure as the callee.

## Composing static calls, bindings, and Boolean branches

The analyzer reads Core Erlang from BEAM debug information. It follows
static calls and propagates values and size bounds through bindings and
Boolean branches. The initial input is a proper integer list, optionally
preceded by an integer key. The composed fragment supports variables,
integer and Boolean literals, proper integer list construction, single-value
bindings, and calls without recursion. Boolean cases include the
compiler-generated truthiness guard used by Elixir `if` when the
condition has been shown to be Boolean.

At each static call, the analyzer substitutes the actual argument values
and sizes. It uses the contracts above for the two built-ins and derives
a bound from the body for a regular callee. Each call bound is included
in the caller's expression under its MFA. If one call prepends a
one-element accumulator through reversal, a later call on the result
receives an input size bound of `n + 1`.

The generated theorem `programValueAndBound` proves that the translated
target agrees with the model and that the modeled cost is at most the
bound for the selected path and the overall bound. Its proof applies the
primitive cost theorems at the derived argument sizes, adds bounds for
sequential costs, and uses the maximum of the branch bounds. Local
call overhead, binding, list construction, and branch operations have
symbolic charges. If an `input_contract` is supplied, the proof uses its
size measure under the stated precondition.

### Conditional reversal

This example composes membership and reversal over an integer key and
a proper integer list.

```elixir
def reverse_on_hit(key, xs) do
  if :lists.member(key, xs), do: :lists.reverse(xs, []), else: xs
end
```

Use `ReductionBounds.infer_list_bound/2` with the function's module,
name, and arity. The generated theorem proves that the function returns
the reversed list on a hit and the original list on a miss. It also
proves the following symbolic bounds. Here
`M(n)` is the refined membership bound and `R(n)` is the reversal bound,
`n` bounds the input list length, and `B_hit` and `B_miss` are
nonnegative symbolic charges for the respective branch operations
outside the calls.

| Result field | Upper bound |
| --- | --- |
| `path_bounds.hit` | `M(n) + (B_hit + R(n))` |
| `path_bounds.miss` | `M(n) + B_miss` |
| `upper_bound` | Maximum of the hit and miss bounds |

Both paths use the same membership upper bound. On a hit, the proof
applies the reversal theorem to the original list and an empty
accumulator, then adds its cost to the membership and branch costs.
On a miss, the proof accounts for membership and the miss branch only.
The `:call_bound` terms in the result keep charges for the two built-ins
separate. The same rules handle a nonempty accumulator and a hit branch
that delegates reversal to a regular helper.

## One CircularBuffer insertion

Call `ReductionBounds.infer_circular_buffer_bound/0` in the test
environment with `circular_buffer` v1.1.0 available. The analyzer checks
the Core Erlang clauses of `CircularBuffer.insert/2` against the state
model and checks the list clauses of `Enum.reverse/1` against its
primitive contract.

The inputs are a buffer with proper integer lists `a` and `b` and an
integer item. A valid state has
`count = length(a) + length(b) <= capacity`, and a nonempty `b`
implies the buffer is full. In the returned formula `n` is the
capacity.

| Path | State update | Symbolic upper bound |
| --- | --- | --- |
| `consume` | Remove the head of `b` and prepend the new item to `a` | `C_consume` |
| `fill` | Prepend to `a` and increase the count | `C_fill` |
| `rotate` | Reverse `a`, drop the oldest element, and start a new `a` | `C_rotate + C_enum_reverse + R(n)` |
| `zero` | Return the original buffer | `C_zero` |

Each path charge includes its local tests and operations outside
the calls listed in its bound. `R(n)` is the existing bound for
`lists:reverse/2`. In the list clauses, `Enum.reverse/1` handles
lists of length at most two locally. For longer lists it calls
`lists:reverse/2` on the suffix after the first two elements, using
those elements in reverse order as the accumulator. Lean proves that
this list model returns the reversed list and that the primitive part
of its cost is bounded by `R(n)`.

`ComposedBound` adds the local and callee charges on the rotation path
and takes the maximum of the four path bounds. Lean proves that the
modeled insertion preserves the state invariant, that a rotation
reverses an `a` of length equal to the capacity, and that the modeled
cost fits the returned bound. At capacity zero, Lean proves that the
state is unchanged and that the cost is `C_zero`.

The Elixir analysis decodes field accesses with `CoreFragment` and
applies the shared `Normalize` rule under the assumption that the
required fields exist in a valid buffer. It compares the resulting
clauses with the expected CircularBuffer conditions and updates.
In `CircularBuffer.lean`, `insertPath` selects the path used by both
`insertModel` and `insertCost`. The Lean cost theorems are stated over
this state model. ExUnit exercises all four paths with the actual library.

### Agreement with a bounded FIFO specification

The specification `fifoInsert` represents the retained items as one
list, in oldest-to-newest order. It appends the incoming item and
keeps the last `capacity` items. For a modeled buffer,
`BufferState.contents` reads `b ++ reverse(a)` in that order.

`insertContents` proves that reading the state after `insertModel`
gives the same list as `fifoInsert` for every valid state and every
integer item. The fill path appends an item without discarding any.
The consume and rotate paths discard exactly the oldest item. The
zero-capacity path retains no items. This theorem connects the
Lean state model to the independent FIFO specification. ExUnit checks
the corresponding observable behavior of the Elixir library.

## Fixed progress and periodic resets

`Periodic.lean` gives the common rule for a sequence of state
transitions with a constant increment and periodic resets. Let `m` be
a positive period, `d` the increment, `o` the lower endpoint after a
step, and `size(s)` the progress in state `s`. The inferred proof
obligations check invariant preservation, `size(s) < m + o` in valid
states, and the following equation for each valid step:

```text
size(s) + d = events_this_step * m + size(next)
```

The next state must also satisfy `o ≤ size(next)`. The rule allows
an initial size below `o` and handles an empty sequence separately.
Lean's `accumulate` combines the transition obligations by induction.
`eventCount` derives `floor(max(initial + n * d - o, 0) / m)`. Here
`initial` denotes the initial size and `n` the number of steps.
`costBound` sums the per-step budgets to give
`n * base + events * surcharge`.

`infer_periodic_bound/2` recognizes a two-argument transition that
adds a positive constant to a pending count. At the threshold it
subtracts the period and returns an event flag. Below the threshold it
keeps the advanced count and returns false. The invariant is
`pending < period`, with a period at least as large as the increment.
For a function that enqueues two items at a time and signals a batch
when it is ready, the rule gives `floor((pending + 2 * n) / period)`.
The counter decoder checks this source shape in Core Erlang. The
counter proof checks the transition's obligations in its natural
number model. The symbolic surcharge is the extra modeled cost of an
event step.

The return value lists `conditions.derived` and `conditions.supplied`
separately. A `periodic_contract` Lean block may specify an extra
predicate `periodicInvariant period state` and a natural-valued
`periodicMeasure period state`. The block proves
`periodicInvariantStep` under `periodicDomain` and
`periodicMeasureBounds` to justify using the measure in place of the
initial pending count. The API returns the supplied Lean source and
separate measured bounds. Lean checks these obligations and rejects a
contract that relies on an unfinished proof or an extra axiom. The
periodic bound tests demonstrate an even-period, even-count invariant
and a measure of `state + 2`.

## Consecutive CircularBuffer insertions

Call `ReductionBounds.infer_circular_buffer_sequence_bound/0` to
derive a bound for `n` calls to `CircularBuffer.insert/2` with integer
items after `CircularBuffer.new(m)` has returned. The analyzer reuses
the single-insertion analysis with `m` as the capacity variable.
It also uses `CoreFragment` to decode the initializer's guard and
checks that the nonnegative integer capacity is stored in an empty
buffer with count zero.

Let `c` be the maximum of the local charges for consuming, filling, and
rotating. Let `r(m)` be the extra cost bound for the rotation's
`Enum.reverse/1` call. This includes its local charge and the existing
`lists:reverse/2` upper bound at capacity `m`.

| Condition | Exact modeled rotations `q(m, n)` | Symbolic cost upper bound |
| --- | --- | --- |
| `m = 0` | `0` | `n * C_zero` |
| `m > 0` and `n = 0` | `0` | `0` |
| `m > 0` and `n > 0` | `floor((n - 1) / m)` | `n * c + q(m, n) * r(m)` |

`CircularBufferSequence.lean` uses the fixed-progress rule with
`size(s) = length(a)`, increment one, and lower endpoint one. Its
`rotationStep` counts a rotation exactly when `insertPath` selects the
rotate path. With positive capacity, an ordinary step increases the
length of `a` by one. A rotation takes place with `length(a) = m` and
leaves the new `a` with length one. `bufferObligations` discharges the
shared rule's premises using the single-insertion model.
`insertManyRotationCount` specializes the shared count theorem to an
empty initial buffer. At capacity zero the state remains empty.

`insertManyCostBound` then combines the per-step cost with the exact
rotation count. The returned `rotation_count` expression uses natural
number subtraction, so `n - 1` is zero when `n = 0`.

### Starting from a valid buffer

Let `a0` be the initial length of the newer list `a`. For any state
satisfying `BufferState.valid`, `insertManyRotationCountFrom` proves
that the modeled number of rotations is zero at capacity zero and
`floor(max(a0 + n - 1, 0) / m)` for `m > 0`. The first rotation takes
place on insertion `m - a0 + 1` if the sequence reaches that point.
Later rotations are `m` insertions apart.

For positive capacity the proof uses
`a0 + n = rotations * m + length(final_a)`. When `a0 + n > 0`, the
final length lies between one and `m`, so subtracting one and dividing
by `m` gives the exact quotient. When `a0 + n = 0`, the run is empty.
At capacity zero the invariant forces both lists to be empty and the
count to be zero. Each insertion leaves the state unchanged.

`insertManyContents` proves that the retained contents after a run
equal a left fold of `fifoInsert`, starting from the initial contents
at the initial capacity. The induction applies `insertContents` at
each step, using preservation of validity and capacity. It covers
the empty insertion list, zero capacity, and nonempty initial buffers.
The equality holds for any assignments of the symbolic charges.

`insertManyLatest` gives the same result directly: concatenate the
initial contents and the incoming items in chronological order, then
keep the last `capacity` items. This includes a sequence of length
zero. Applying the theorem to any prefix gives the retained contents
at that point in the run, including runs that cross a rotation.

`insertManyCostBoundFrom` bounds the modeled cost by
`n * c + rotations * r(m)` for positive capacity and `n * C_zero`
at capacity zero. The existing empty-initialization theorems specialize
these results to `a0 = 0`. The public inference entry point still
returns the bound for a run starting from `new/1`.

ExUnit checks states reached by insertion into the actual library for
capacities zero through five. It compares observed rotation counts
with the formula and compares the contents after each insertion with
a FIFO list that discards its oldest item at capacity.

## Reproduce the case studies

With the project's test dependencies installed, including
`circular_buffer` 1.1.0 and the Lynx toolchain, run:

```sh
mix test --only case_study
```

The six tagged tests in `test/reduction_bounds_test.exs` also run in
`mix test`. They call the public inference functions and check the
returned formulas, input domains, size measures, and proof reports.
They also exercise the actual Erlang or Elixir functions with boundary
inputs and compare buffer contents with a FIFO list.

Each inference call enters the common `verify_bound` path. This path
selects the source for the case, sends the resulting postlude to the
Lynx runner, and asks Lean to audit the named theorems for unexpected
axioms. A successful result records the audited names in
`checked_theorems`. The tests check those names, the postlude identity,
and its successful status. Named theorem checks reject dependencies
on unfinished proofs such as `sorryAx`.

| Case | Source checked | Rules and contracts reused | Lean evidence |
| --- | --- | --- | --- |
| `lists:member/2` | Lynx's bundled value model | Empty, stop, and tail-step rules of `ListCost` | `searchCostDerivation`, `listRulesSound`, `listPathBounds`, `listValueAndBound` |
| Conditional reversal | Lynx translation of the compiled test function | The refined membership bound on both paths, reversal with an empty accumulator on a hit, sequential addition, and the maximum of the branch bounds | `Member.listValueAndBound`, `Reverse.listValueAndBound`, `programValueAndBound` |
| One insertion | Buffer state model selected by checking the Core Erlang clauses | The list clauses of `Enum.reverse/1`, the reversal contract, and the maximum of the four path bounds | `enumReverseListValue`, `enumReverseCostBound`, `bufferRotationSize`, `insertCostBound`, `insertContents` |
| Consecutive insertions | The same state model and a checked empty initializer | Single-insertion budgets, invariant preservation, and the common periodic reset rule | `bufferObligations`, `Periodic.eventCount`, `Periodic.costBound`, `insertManyRotationCountFrom`, `insertManyCostBoundFrom`, `insertManyLatest` |

The tagged reversal test checks the auxiliary `lists:reverse/2`
contract independently. The tests also compare each embedded
`:call_bound` expression with its primitive formula. The buffer shape
checks are performed by the Elixir analyzer. The corresponding Lean
theorems range over the buffer state model, and ExUnit exercises the
actual library on the specified examples.

### Built-in contracts and Lynx laws

`lists:member/2` and `lists:reverse/2` enter the analysis through their
bundled `Erlang.lists` definitions. Their cost recurrences belong to
`reduction_bounds`. Membership requires an integer key and a proper
integer list, and returns an atom indicating whether an exact match
exists. Reversal requires two proper integer lists and returns the
reverse of the first followed by the accumulator. Both contracts
use an upper bound on the length of the list they traverse and
allow arbitrary natural-valued symbolic charges. Each continuation
consumes one cell. Lean checks each result equation and cost
inequality against the corresponding model.

In a [Lynx law][lynx-laws], `requires:` expresses a Boolean predicate on
Erlang inputs, and `expects:` expresses a Boolean property of the
successful computation. The following are specifications that can
be stated in that form, using helpers for the input predicates and
reference results. The tagged suite checks the generated Lean
theorems listed above.

| Case | Condition expressible in `requires:` | Value property expressible in `expects:` |
| --- | --- | --- |
| Membership | Integer key, proper integer list, and list length at most `n` | The returned Boolean equals a reference exact-membership implementation |
| Reversal contract | Proper integer lists for the input and accumulator, with input length at most `n` | The result equals the reversed input followed by the accumulator |
| Conditional reversal | Integer key and proper integer list of length at most `n` | The result equals the reverse on a hit and the input on a miss |
| One insertion | Valid buffer state with integer elements and an integer item | The result is valid and its contents equal one bounded FIFO insertion |
| Consecutive insertions | Nonnegative capacity and a proper integer list of items | The retained contents equal the latest `m` items after the insertions |

Translation support is required for a law's helpers and target.
For the buffer cases, the value properties in the table describe the
state-model theorems. The Lean cost obligations are separate
inequalities over costed models, including the per-cell charges,
static call bounds, rotation budget, and count of rotations. The
law vocabulary can express a numeric bound when an explicit cost
function is available. A value law alone observes the result of the
computation, while the inequalities here relate that result model
to a separately defined symbolic cost.

[lynx-laws]: https://github.com/josevalim/lynx/blob/d74890ac7a446d57b762d0e4fcd3c848146b2ff6/README.md#getting-started-with-proofs

## Scope

The inequalities bound the symbolic cost model. To obtain an upper
bound for ERTS reductions, a separate proof must relate the charges to
the accounting of the target ERTS build, including when the built-in
yields and resumes under a fresh reduction budget.

## Cost safety for finite protocol traces and prefixes

`ProtocolCost.new/2` associates every owned state/event context with a
nonnegative cost expression and a counter. Constants and participant-scoped
symbolic charges can be combined by addition, multiplication, and maximum.
Data references use both byte length and structural size; integer references
use the magnitude bit-length bounds from `IntegerSize`. A reference must be
required by the corresponding condition rule. Environmental observations
cannot be assigned work. A counter must count that context, including the
state-dependent distinction between a fresh submission and its resumption.

For participant `p` and counter `k`, let `M(p,k)` be the maximum of the
capped expressions assigned to that pair, and `N(k)` its declared finite
count limit. The generated budget is

\[
 B_p=\sum_k N(k)M(p,k).
\]

Capping replaces each size reference by its supplied upper bound. The
expression language is monotone in these nonnegative parameters, even for
products. Alternatives share a maximum; they are not all charged at each
occurrence. An event contributes its expression only to its unique owner.
Participant budgets retain their declared cost units and are not added
across participants. Participants without modeled work events are reported
as `unmodeled_participants`, without a claim about their actual work.

In `ProtocolCost.lean`, `featureBound` connects the row conditions to actual
size parameters. `Expr.monotone` and `localBound` bound each local event.
`traceBound` sums these inequalities; `costSafety` applies the finite counter
limits. `prefixCostLe` proves that taking any aligned prefix cannot increase
the cost. `prefixCostSafety` therefore establishes the same budget for every
prefix of any finite trace satisfying the supplied size and count conditions.
The empty trace and prefixes ending in suspended or waiting states are
included. No terminal-state premise is required.

`ProtocolCostProof.build/3` emits `suppliedCostCertificate`, checking complete
work-context coverage, feature permissions, counted contexts, and budget
groups. `suppliedCostSafety` and `suppliedPrefixSafety` quantify over arbitrary
finite event, state, and observation lists under `RowsHold` and `CountsHold`;
they are not restricted to the example trace. Protocol validity is checked
separately by the existing `Protocol` certificate. For a valid execution,
these theorems apply to its certified event/state sequence. Generated
`suppliedBoundMatches` theorems also check that the returned Elixir formulas
are exactly Lean's `boundExpr`. `suppliedTraceBudget` and
`suppliedTracePrefixes` specialize safety to the supplied trace. Selected
proof dependencies are audited against the existing axiom allowlist.

Constructors return `lean_status: :not_checked`; constructing a proof does
not execute Lean. To run the checks, pass the generated proof through
`ProofInput.protocol_cost_postludes/1`, assemble it with `ProofInput`, and
run `Lynx.Commands.verify!/2`, as demonstrated by the proof test.

Reproduce the tests with:

```sh
mix test --only protocol_cost
```

The tests include empty traces, suspension before completion, rejected
submissions followed by retries, receive inspections and successful responses,
large integer bounds, and symbolic charges. Negative checks reject missing
work rules, charges on environmental events, unsupported size references,
counters that do not count a context, forged formulas, altered evidence,
and unfinished proofs. These results concern the declared symbolic cost
semantics. Association of observations with real data, source-code
correspondence, concrete reduction accounting, and wall-clock time remain
outside the proof. Bounded finite-trace work does not prove eventual response,
scheduling, timeout completion, or any other progress property.

## Port transitions and conditional completion

`PortProtocol.new/0` now also distinguishes decoding failure and an
application receive timeout. The supported terminal states are:

| Final state | Observed outcome | Final caller event |
| --- | --- | --- |
| `:complete` | `:success` | `:decode` |
| `:failed` | `:rejected` | `:return_rejection` |
| `:closed` | `:port_closed` | `:handle_closure` |
| `:timed_out` | `:timeout` | `:handle_timeout` |
| `:decode_failed` | `:decode_error` | `:decode_error` |

The environment event `:timeout_elapsed` is allowed only while awaiting a
response, followed by caller-owned timeout handling. This represents an
application's receive-timeout protocol, not a timeout option of
`port_command/2,3`. It cannot interrupt a suspended submission. Closure,
arrival, and timeout observations have no owned work charge; their handlers
have separate caller cost expressions. Decoding failure uses the independent
response-size conditions. Every new work context must have an explicit cost
rule, so its cost cannot silently be omitted from a participant budget.

### The termination measure

`PortCompletion.lean` defines a `Configuration` containing the protocol state
and remaining allowances for rejected outcomes, submission resumptions, and
receive inspections (including the matching response). These allowances are
separate from a retry count: a final rejected submission consumes an allowance
even if it is returned instead of retried. With remaining allowances `R`, `S`,
and `I`, the rank is

\[
 \rho(s)=10(R+S+I)+p(s), \qquad
 0\leq p(s)\leq9.
\]

Here `p(s)` is the protocol phase. The initial phase is 9. Local phases order preparation, submission, response
handling, and terminal handling. Every cycle consumes an allowance; all other
transitions strictly decrease the phase. `Ranked` checks these properties
against every transition in the supplied Port contract. `Advance` requires an
allowed transition and exact allowance balances. `advanceDecreases` proves
strict rank decrease. `checkMovesSound` checks the entire supplied sequence
of configurations, and `Moves.erased` connects it back to the shared protocol
`Runs` relation. `Moves.bounded` bounds active events by the initial rank.
`acceptedPreserves` and `noRetransmission`, under `PostAcceptanceSafe`, prove
that after acceptance the protocol stays in the later states and cannot
submit or retry another request. The generated certificate checks this
condition against the supplied transition table.

### Explicit progress assumptions

`Behavior` describes an arbitrary infinite sequence of observations. A tick
with no event leaves the configuration unchanged. An active tick must satisfy
`Advance`; terminal configurations may remain idle forever. Thus the model
permits arbitrary finite idle delays without treating waiting as active work.
The `Progress` proposition requires an eventual next active event in each
nonterminal state, according to four separate hypotheses:

| Declaration | Lean field | Applicable states |
| --- | --- | --- |
| `:caller_progress` | `caller` | Preparation, retry/rejection handling, retrieval, decoding, and terminal handling |
| `:submission_progress` | `submission` | Submission returns an outcome or observes closure |
| `:resumption_progress` | `resumption` | Suspended submission eventually resumes or observes closure |
| `:response_progress` | `response` | Waiting eventually observes a response, closure, timeout, or a permitted inspection |

Each eventual event must respect the protocol and remaining allowances.
Repeated inspections cannot indefinitely substitute for response progress,
because they consume a finite allowance. Likewise, rejection and suspension
cycles cannot continue indefinitely. These are assumptions about the complete
behavior, not facts inferred from the observed prefix. A bounded external
computation is neither required for the caller cost proof nor sufficient to
establish these progress hypotheses.

`behaviorInvariant` preserves declared states. `conditionalCompletion` uses
strong induction on the rank and the progress assumptions to prove that a
terminal state is eventually reached. `eventCountBound` bounds the active
events in every finite prefix by `9 + 10*(R + S + I)`. This bounds neither the
number of idle ticks nor elapsed time. `stalledNotComplete` exhibits permanent
idle waiting without completion; finite cost safety alone cannot exclude it.

Termination does not imply a successful response. `successfulCompletion`
additionally requires `NoFailure`: no final rejection, closure handler,
timeout handler, or decoding-failure event occurs. `SuccessSpec` checks that
these are exactly the ways to enter the failure terminal states. This
additional assumption includes successful decoding and exclusion of the
supported error outcomes; it is not derived from acceptance of a command.

### Construction, evidence and diagnostics

For an existing Port cost profile `profile` and supplied `events` and
`observations`, build completion evidence as follows:

```elixir
options = [
  limits: %{rejections: 2, resumptions: 3, inspections: 8},
  progress: [:caller_progress, :submission_progress,
             :resumption_progress, :response_progress],
  goal: :termination
]
{:ok, result, proof} = ReductionBounds.PortCompletionProof.build(
  profile, events, observations, options)
result.completion.status
#=> :conditional
result.completion.active_event_bound
#=> 139
{:ok, postludes} = ReductionBounds.ProofInput.port_completion_postludes(proof)
translation = Lynx.Translation.new(postludes: postludes)
project = Path.join(Mix.Project.deps_paths()[:lynx], "Lean")
reports = Lynx.Commands.verify!(project, ReductionBounds.ProofInput.assemble(translation))
```

`PortCompletion.check_trace/4` and the proof builder retain `lean_status:
:not_checked`; inspect the Lean reports to establish that proof checking
succeeded. `:conditional` means the requested hypotheses were declared and
the supplied trace respects the completion allowances. It is not a proof
that a real environment satisfies those hypotheses. The generated
`suppliedConditionalCompletion` has explicit `Behavior`, initial-configuration,
and `Progress` hypotheses; the declarations do not introduce progress axioms.
For `goal: :success`, add `:no_failure_outcomes` to the declarations. Only
then is `suppliedSuccessfulCompletion` emitted, still with an explicit
`NoFailure` premise.

When assumptions or allowances are missing, the result reports
`:insufficient_assumptions` and lists them. It still returns the independent
participant cost formulas and generates the cost proofs, but emits no
supplied completion theorem. Exhausted allowances report
`:inconsistent_limits` with the failing occurrence. Requesting success after
an observed failure reports `:inconsistent_assumptions`. The observed outcome
of the supplied trace is reported separately from the conditional theorem.
External work remains `:not_bounded`, and external progress declarations are
reported individually as assumed or missing.

`suppliedTerminalBudget` applies the existing universal cost theorem to every
supported terminal outcome under `RowsHold` and `CountsHold`. The cost
conditions are independent of the progress hypotheses: the rank's event bound
does not automatically establish a user's tighter size or counter limits.
The completion theorem concerns arbitrary behaviors; the cost theorem
concerns their finite event traces when those conditions hold. Generated
configuration, rank, terminal-cost, and completion theorems are audited
against the existing axiom allowlist.

Reproduce the new and regression checks with:

```sh
mix test --only port_completion
mix test --only protocol_model
mix test --only protocol_conditions
mix test --only protocol_cost
```

Tests exercise every supported terminal outcome, suspension, retry, unrelated
message inspections, successful completion assumptions, missing progress,
exhausted allowances, and invalid transitions. Lean independently rejects
altered transitions, rank bounds, and unfinished certificates. A permanent
waiting example is checked, while an unconditional completion claim for that
example is rejected. The results concern the supplied external Port protocol
model. The source-fragment checks below connect finite normally returning
client executions to that model, but do not transfer the completion theorem
to actual receive helpers. Framing/matching correctness, external-program and
linked-in driver behavior, concrete ERTS charging, OS scheduling, delivery
guarantees, and deadlines remain unverified.

## Connecting a supported Core Erlang client to the Port model

`ReductionBounds.infer_port_bound/3` adds source correspondence for a finite
client fragment. The input is the target MFA, a `ProtocolCost` profile for
`PortProtocol.new/0`, and explicit helper contracts. A successful result has
`source_correspondence: :checked` only after Lean verifies the generated
connection and bound. Proof builders and `PortSource.infer/3` return pending
evidence with `lean_status: :not_checked`; they do not establish a bound by
constructing a candidate alone.

### Accepted client and call contracts

The first argument is the Port and the second is preparation input. A typical
accepted body is:

```elixir
def request(port, input) do
  prepared = Helpers.prepare(input)

  case :erlang.port_command(port, prepared, [:nosuspend]) do
    true ->
      case Helpers.await_reply(port) do
        {:data, data} -> Helpers.decode(data)
        :closed -> :closed
        :timeout -> :timeout
      end
    false -> :rejected
  end
end
```

The preparation binding, Port argument, prepared request, reply binder and
decoder argument are checked. Boolean clauses and the three disjoint reply
patterns may be reordered. Guards must be literal true. The compiler's final
case-failure clause must have the recognized generated shape; it is excluded
under the declared result contracts. There is no silent fallback for an
unsupported expression. Errors retain the target and a path such as a binding,
subject, argument, or response branch.

Helper declarations have the form:

```elixir
calls = %{
  prepare: {Helpers, :prepare, 1},
  reply: {Helpers, :await_reply, 1},
  decode: {Helpers, :decode, 1}
}
{:ok, bound} = ReductionBounds.infer_port_bound(
  {Client, :request, 2}, profile,
  calls: calls, beam_binaries: beams, timeout: 60_000)
bound.source_correspondence
#=> :checked
bound.source_node_bound
#=> 25
```

Here `profile` is the explicit `ProtocolCost` profile from the preceding
sections. It must cover every work context, including failure handling.
`beams` contains the target's compiled binary for an in-memory module; it may
be omitted for modules with readable BEAM files on the code path. Standard
verification timeout, concurrency and Lean options apply. The test fixture
`test/fixtures/port_client.ex` supplies both the normal and reordered clients,
and `mix test --only port_source` reproduces their checks. The fixture is
compiled once by `test_helper.exs`, and the tests retain its BEAM binaries.

`Contracts` is an explicit Lean hypothesis over the external-call relation.
It states, for each registered call, that the returned value has the allowed
shape and its modeled work events form a protocol run between the stated
entry and exit states:

| Role | Entry | Normal result | Exit |
| --- | --- | --- | --- |
| Prepare | idle | Any modeled value | prepared |
| Submit | prepared | true / false | awaiting response / rejected |
| Reply | awaiting response | data / closed / timeout | response received / closed / timed out |
| Decode | response received | Any modeled value | complete |

The submit role is fixed to `erlang:port_command/3` with the `nosuspend` option.
Helper roles must have distinct registered names and arity one. Reply traces
may include finite unrelated-message inspections and explicit response,
closure, or timeout handling; their counts and data sizes still require the
independent profile conditions. Call-event charges must cover the contracted
helper or primitive work. Unknown external-program work remains outside the
caller budget. A helper's implementation is not verified by declaring its
name: `call_contracts` records `status: :assumed` and normal-return totality as
`:not_established`. A valid Port, permitted caller/owner relationship, framing,
matching, size bounds, and coverage of actual helper work remain applicability
conditions. No encoding or response-size relation is inferred from the request.

### Checked connection and source costs

`PortSource` reads the target through the existing BEAM debug-information
path. It reifies accepted Core blocks without source annotations, retaining
static call identities, pure arguments, variable bindings, Boolean clause
order and reply-pattern order. The `Core` semantics in `PortSource.lean`
evaluates these blocks using mathematical values, an environment and an
external-call relation. Opaque values represent input Ports and payloads;
the theorem does not establish a concrete runtime representation relation.
The source execution records returned values, ordered call occurrences and
local work. Calls do not acquire protocol correctness merely from their names.

The separate `Program` semantics attaches roles and protocol events. `Connect`
checks all control arms and exact argument routing. `ReturnShape` restricts
pure returns to final rejection handling or an already terminal state;
a return cannot invent arbitrary communication events. `RegistryValid` checks
distinct role identities. The generated `suppliedConnection` is a Lean proof
of this relation, not an unchecked status flag from Elixir.

`sourceAgreement` proves that each finite normally returning source execution
has a model execution with the same value, variable bindings, call order and
local work. `modelSafe` composes the declared call contracts and proves that
the resulting trace is admitted by the shared Port protocol and reaches a
supported terminal state. This proves the connection for every source
execution in the stated fragment under the contracts, not just for one
selected success trace.

Local source work is charged separately so that bindings, argument retrieval
and case dispatch are not omitted. In the abstract semantics, returning a
value costs one local unit; a preparation binding costs `2 + arity`; Boolean
dispatch costs `4 + arity`; reply-pattern dispatch costs `9 + arity`; a tail
call costs `1 + arity`. The work of nested expressions is added. `Core.budget` adds the
budgets of all alternatives, giving a conservative finite limit `L`.
`localBound` proves that every source derivation has local work at most `L`.
For the example, `L = 25`. With a natural symbolic local-unit charge
`source_node` (written as `c_s` below), and protocol budget `B_p`, the caller formula is

\[
 B_s = L c_s + B_p.
\]

The returned Elixir expression has the form:

```elixir
{:add, {:mul, 25, {:charge, :source_node}}, protocol_formula}
```

`connectedCostBound` combines local-work safety with the universal protocol
cost theorem under `RowsHold` and `CountsHold`. `suppliedLocalBudget` checks
the reported `L`. `suppliedSourceFormulaMatches` checks that the returned
formula is exactly the local budget plus the checked protocol formula.
`suppliedSourceAgreement` and `suppliedSourceBound` specialize the shared
theorems to the extracted target. All selected theorem dependencies, including
connection certificates, are audited against the existing axiom allowlist.
These are symbolic units, with no claim that a local unit is an ERTS reduction.

### Scope, diagnostics and reproduction

This stage connects finite normally returning client executions. It does not
prove that calls return, nor connect unfinished source execution prefixes
inside an opaque receive helper. Protocol-level prefix safety remains
available under its earlier conditions. Helper exceptions, decoding failures
that raise, native Core receive loops, recursion, dynamic calls, blocking
submission, arbitrary guards and unsupported arguments are rejected or
explicitly outside the checked source claim. The caller result records
`execution_domain: :finite_normal_executions_under_call_contracts`, assumed
helper contracts, unresolved source-prefix and exception obligations, and
unverified runtime and timing correspondence. The earlier model-level
conditional completion theorem is not automatically a source termination
proof.

BEAM extraction, recognition of accepted Core blocks, abstraction of runtime
values, and serialization remain trusted. Lean checks the reified Core-to-model
connection and mathematical semantics; it does not certify the BEAM debug
backend, the Elixir reifier, a concrete ERTS build or external helper code.
Unsupported code and wrong Port/request/reply arguments fail with source paths
instead of falling back to a checked model-only result for that target.

```sh
mix test --only port_source
```

Positive checks use compiled BEAM for both clause orders and exercise the
public verification API. Negative checks reject missing or mismatched helper
contracts, wrong Port routing, blocking commands and native receive syntax.
Lean independently rejects altered helper identities, submission options,
Boolean orientation, primitive identities, local limits, returned formulas
and unfinished connection certificates. No test launches an external Port
program or measures reductions.

## Port API, diagnostics and reproducible evaluation

The [Port guide](examples/ports.md) provides complete profile declarations and
public API examples. `verify_port_model/3` verifies a supplied model trace,
finite-trace and prefix cost safety, and optional conditional completion.
`infer_port_bound/3` checks the supported Core client correspondence and caller
bound. Both use the existing bounded verification runner and reject empty or
failed Lean reports. Constructors and proof builders remain unchecked until
that runner succeeds. Event names are resolved through the registered Port
contract; event structs retain their ownership checks.

Public results now share the reporting conventions of the contract workflow:

| Field | Model check | Source check |
| --- | --- | --- |
| `verification_scope.kind` | `:supplied_port_model` | `:core_connected_port_client` |
| `source_correspondence` | `:not_checked` | `:checked` for the supported fragment |
| Cost claim | All modeled finite traces and prefixes under conditions | Finite normally returning source executions under call and profile conditions |
| Completion scope | Protocol model only | Source completion not established |
| `checked_theorems` | Protocol, condition, cost, and applicable completion theorems | Protocol, condition, cost, and Core connection theorems |

`verification_scope` records checked claims, conditional claims, assumptions,
trusted processing and unresolved obligations separately. The original source
execution-domain label is retained in `execution_domain`. Source results remove
the empty profile-validation trace, so it cannot be mistaken for an observed
target execution. Source-prefix, exception and helper-totality obligations
remain explicit. A source result does not inherit the model completion theorem.

Model diagnostics distinguish missing completion hypotheses from inconsistent
limits and a failed outcome that conflicts with requested success. A checked
cost bound can still be returned in those cases. `completion.theorem_status`
is `:checked_under_assumptions` only when the applicable completion theorem
was generated and checked; `actual_completion` remains `:not_established`.
External behavior and environment progress are assumptions, not proven facts.
Missing size/cost conditions or exceeded cost-profile counters instead prevent
verification. Event and target errors retain the offending occurrence or source
path. Unknown event names and option keys have explicit tuple diagnostics.
Forged checked flags do not replace fresh validation and proof checking.

The workflow tests use a declared event cost of `event_work` plus the bounded
byte and structure dimensions. With all symbolic charges set to one, the
reproducible profile budget is 1156 symbolic units. The supported client adds
25 local source units, giving 1181. These numerical interpretations are
examples of the formulas, not measurements or ERTS reduction budgets.

```sh
mix test --only port_workflow
REDUCTION_BOUNDS_REPORT=1 mix test --only port_workflow
```

Each path is an independent bounded verification test. The reports include
formulas, conditions, supported and observed outcomes, progress hypotheses,
checked theorem names, and diagnostics. Existing `protocol_model`,
`protocol_conditions`, `protocol_cost`, `port_completion`, and `port_source`
tags reproduce the lower-level positive and altered-evidence checks. The
public workflow covers all supported terminal outcomes, unfinished waiting,
retry and receive inspection paths, missing progress, conflicting completion
conditions, unsupported target routing and source/model scope separation.
It does not execute an external Port program, validate actual helper contracts,
connect arbitrary Core receive code, or establish runtime/time correspondence.
