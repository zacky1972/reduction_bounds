# Symbolic list bounds

`infer_list_bound/2` returns a Lean-checked `refined_upper_bound` alongside
`upper_bound`. For an input length at most `n`, a traversal takes at most
`n` recursive steps before reaching the empty list, or at most `n - 1`
before stopping on a nonempty list. For positive `n`, the refined bound
takes the maximum of these two path bounds when both are possible. At
`n = 0`, it uses only the empty-list cost.

The proof is parametric in nonnegative symbolic charges. Applying it to
actual BEAM reductions requires a separate, version-specific argument.
That argument must map compiled instructions and runtime paths to the
modeled charges, account for every reduction in the measurement interval,
and justify each charge bound under the permitted VM states. Relevant
conditions include available reduction budget, integer representation,
and whether collection occurs during the call.

## Examples and verification cases

The `ReductionBounds` module documentation includes executable examples
for list traversal, input contracts, and forwarding calls. The proof
reference describes the supported shapes and assumptions:

- [User-defined traversals](../proof.md#user-defined-list-traversals).
- [Built-in membership](../proof.md#listsmember2).
- [List reversal](../proof.md#listsreverse2).
- [Input contracts and forwarding calls](../proof.md#input-contracts-and-forwarding-calls).
- [Conditional reversal](../proof.md#conditional-reversal).

Run the library's compiled verification cases from the repository root:

```sh
mix test --only case_study --trace
```

For all supported symbolic cost models, a successful proof applies under
its recorded assumptions. Mapping those charges to a particular ERTS
build is a separate obligation.
