# ReductionBounds

`reduction_bounds` is an experimental Elixir library for deriving symbolic
cost bounds for supported Erlang and Elixir functions and checking them
in Lean. Relating those bounds to reductions charged by a concrete BEAM
runtime remains separate work.

## Installation

Use Git and Elixir 1.20 or later in the 1.x series with a compatible
Erlang/OTP version. Install [Elan](https://github.com/leanprover/elan),
Lean's toolchain manager, and ensure `lean` and `lake` are on `PATH`.

Add the GitHub `main` branch to `deps/0` in your project's `mix.exs`:

```elixir
{:reduction_bounds, github: "zacky1972/reduction_bounds", branch: "main"}
```

From your project's root, fetch dependencies and install the exact Lean
toolchain required by the fetched Lynx checkout:

```sh
mix deps.get
export ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)"
elan toolchain install "$ELAN_TOOLCHAIN"
lean --version
lake --version
mix compile
```

Set `ELAN_TOOLCHAIN` from that file in each shell used for building or
proof checking, unless your project has a matching `lean-toolchain` file.
See [toolchain maintenance](docs/toolchains.md) for Elan and Lynx updates
and instructions for working in this repository.

## Getting started and Case Studies

Follow [Getting Started](docs/getting_started.md) to install the toolchain,
check your first bound, and read the result's proof scope.

The [Case Studies](docs/case_studies.md) provide compiled-source and IEx routes
for constants, branches, recursion, list traversal and conditional reversal,
integer sizes and contract reuse, CRC/variance kernels, maps, periodic rules,
ring buffers, Port and RPC workflows. The [examples index](docs/examples.md)
links to detailed API guides.

The [proof reference](docs/proof.md) explains the checked theorems,
assumptions, and reproduction commands. Future directions are in the
[roadmap](docs/roadmap.md).

## Limitations

- Analysis requires Core Erlang recoverable from BEAM debug information.
  Stripped binaries and unsupported source constructs are outside the
  current scope.
- Target modules normally need readable `.beam` files on the code path.
  For modules compiled in IEx or with `Code.compile_string/1`, retain and
  pass their binaries using `beam_binaries`, including dependencies that
  exist only in memory.
- Paths that use Lynx translation are subject to its supported constructs
  and dependency-cycle checks. Translating `Enum.map/2` can encounter a
  cyclic module dependency even when intended inputs are lists. See the
  [verification guide](docs/examples/verification.md#translation-limitations).
- A successful result applies to its mathematical model under the reported
  input and callee conditions. Contract labels such as `:jit` do not prove
  runtime applicability. Concrete reduction accounting, wall-clock timing,
  and scheduling guarantees require separate evidence.

## License

Copyright 2026 University of Kitakyushu.

Licensed under the Apache License, Version 2.0. See [LICENSE.md](LICENSE.md).


### RPC prototype workflows

`ReductionBounds.verify_rpc_model/4` verifies supplied mailbox timelines and
participant budgets with separate conditional completion reporting.
`ReductionBounds.verify_rpc_conditions/4` checks the mailbox/completion model
without cost declarations. `ReductionBounds.infer_rpc_bound/3` checks the
restricted helper-contracted source fragment under explicit applicability and
mailbox association conditions. See the [public RPC guide](docs/examples/rpc_workflow.md)
for setup, supported forms and evidence reporting. Model completion is distinct
from source totality; native source receive is currently unsupported.
