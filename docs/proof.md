# Proof of the symbolic bound for lists:member/2

Call `ReductionBounds.infer_list_bound({:lists, :member, 2})` to check
the bound for the Erlang built-in. The analysis uses the built-in value
model `Erlang.lists.«member/2»` supplied by Lynx. The inputs in the
theorem are an integer key and a proper list of integers, encoded as
Lynx terms. The size parameter `n` is any natural number at least as
large as the input list length.

## Value agreement

The costed model returns a pair consisting of the Boolean result as a
Lynx atom and a symbolic cost. It returns `false` for an empty list,
returns `true` at the first element exactly equal to the key, and
otherwise continues on the tail. Lean proves by induction on the input
list that the value component agrees with the result of the Lynx model.
In the inductive step, exact comparison of two encoded integers reduces
to equality of their integer values.

## Cost recurrence

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

## Upper bounds

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

## Scope

The inequalities bound the symbolic cost model. To obtain an upper
bound for ERTS reductions, a separate proof must relate the charges to
the accounting of the target ERTS build, including when the built-in
yields and resumes under a fresh reduction budget.
