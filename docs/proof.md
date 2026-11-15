# Proofs of symbolic cost bounds

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
`M(n)` and `R(n)` are the proved upper bounds for membership and reversal,
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

The proof in `CircularBufferSequence.lean` threads the state after
each insertion into the next call. Its `rotationStep` counts a
rotation exactly when the shared `insertPath` selects the rotate path.
For positive capacity, a step without rotation increases the length of
`a` by one. A rotation takes place with `length(a) = m` and leaves the
new `a` with length one. Starting with an empty `a`, the theorem
`insertManyFromPositive` gives
`n = q * m + length(final_a)`. For a nonempty insertion sequence,
`length(final_a)` lies between one and `m`, so
`insertManyRotationCount` derives the quotient in the table. At
capacity zero the state stays empty on every step.

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

## Scope

The inequalities bound the symbolic cost model. To obtain an upper
bound for ERTS reductions, a separate proof must relate the charges to
the accounting of the target ERTS build, including when the built-in
yields and resumes under a fresh reduction budget.
