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

## Examples and verification cases

Start with the [examples index](docs/examples.md). It links to guides for
Lean verification, symbolic list bounds, and cost-contract comparison and
bound reuse, as well as the integer, CRC, map, and ring-buffer cases.

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
