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
is described below. Inference from program expressions and operation-cost
contracts are subsequent work. No immediate-integer threshold or ERTS reduction
accounting is assumed here.

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

Constant left shifts and low-bit masks are described below. Right
shifts, general bitwise operations, branch refinement, propagation through
program bindings and calls, recursive size invariants, and size-dependent
operation-cost contracts remain subsequent work. No runtime word size,
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
Variable shift amounts, right shifts, XOR and other general bitwise
operations, automatic Core Erlang propagation, and size-dependent cost
contracts remain subsequent work. These rules introduce no immediate
integer boundary or concrete ERTS reduction charges.

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
