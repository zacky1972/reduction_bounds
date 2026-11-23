# Examples and verification cases

Start with one of these guides after completing the installation in the
[README](../README.md#installation). Interactive examples run in
`iex -S mix`; test commands run from the repository root.

| Guide | Purpose |
| --- | --- |
| [Verify Lean declarations](examples/verification.md) | Supply a proof for a translated function, including a module compiled in IEx |
| [Compare cost contracts and reuse a verified bound](examples/cost_contracts.md) | Derive an integer cost bound, compare contracts, and transfer the bound |
| [Port models and supported clients](examples/ports.md) | Check finite traces, conditional model completion, and a supported Core Erlang client |
| [Symbolic list bounds](examples/list_bounds.md) | Understand traversal bounds and find list, input-contract, and composition examples |

The module documentation contains additional API examples. The
[proof reference](proof.md) records what Lean checks and which conditions
remain assumptions. The following cases reuse those proof rules:

| Verification case | Detailed account |
| --- | --- |
| Integer sizes, arithmetic, variance, and CRC expressions | [Integer costs](proof.md#integer-sizes-connected-to-symbolic-costs) |
| Membership, reversal, and conditional reversal | [List bounds guide](examples/list_bounds.md) |
| Map and struct operations | [Map and struct proofs](proof.md#map-and-struct-operations) |
| One ring-buffer insertion | [Single-insertion model](proof.md#one-circularbuffer-insertion) |
| Consecutive ring-buffer insertions and FIFO contents | [Insertion sequences](proof.md#consecutive-circularbuffer-insertions) |
| Fixed progress and periodic resets | [Shared transition rule](proof.md#fixed-progress-and-periodic-resets) |
| Port outcomes, finite prefixes, and supported client correspondence | [Port workflow](examples/ports.md) |
| Contract comparison and verified bound reuse | [Public API evaluation](proof.md#public-api-integration-and-evaluation) |

To print the integer workflow's upper-bound formulas, contracts,
conditions, and checked theorem names:

```sh
REDUCTION_BOUNDS_REPORT=1 mix test --only cost_contract_workflow --trace
```

To print the Port workflow's formulas, conditions, completion assumptions,
verification scopes, diagnostics, and checked theorem names:

```sh
REDUCTION_BOUNDS_REPORT=1 mix test --only port_workflow
```

To reproduce the tagged list and ring-buffer verification cases:

```sh
mix test --only case_study --trace
```

These commands evaluate mathematical cost models. They do not measure
runtime reductions or execution time. See the [roadmap](roadmap.md) for
work beyond the checked prototype.
