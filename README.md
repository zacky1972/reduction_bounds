# ReductionBounds

`reduction_bounds` is an experimental Elixir library for deriving symbolic
upper bounds on the number of reductions that BEAM charges for a function
call or a sequence of calls. The project is in early development.

A bound describes how the reduction count depends on inputs and their
preconditions, such as a maximum list length. A bound in reductions
expresses work in BEAM's scheduling units. Turning it into a bound on
elapsed time requires separate, platform-specific timing evidence.

## Installation

Use [Git](https://git-scm.com/) and Elixir 1.20 or later in the 1.x series
with a compatible Erlang/OTP version.

### Lean prerequisites

Install [Elan](https://github.com/leanprover/elan), Lean's toolchain manager,
and ensure that its `lake` executable is on `PATH`. Lynx uses Lake to
build its Lean components and run proof checks.

### Install from GitHub

Add the following entry to `deps/0` in your project's `mix.exs` to
install from the `main` branch.

```elixir
{:reduction_bounds, github: "zacky1972/reduction_bounds", branch: "main"}
```

Run the following commands from your project's root. Mix fetches Lynx
as a dependency of `reduction_bounds`. The fetched Lynx checkout
specifies the required Lean toolchain.

```sh
mix deps.get
export ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)"
elan toolchain install "$ELAN_TOOLCHAIN"
lake --version
mix compile
```

Set `ELAN_TOOLCHAIN` from the same file in each shell where you build the
project or run Lynx-based verification. The [Lynx revision recorded in
this repository's lockfile](https://github.com/josevalim/lynx/blob/d74890ac7a446d57b762d0e4fcd3c848146b2ff6/lean-toolchain)
uses Lean 4.35.0 (`leanprover/lean4:v4.35.0`).

## Verify Lean declarations

The current API checks caller-supplied Lean declarations against functions
translated by Lynx. Automatic derivation of reduction bounds is planned.

For a proof stored in the project's `lean/` directory, call
`ReductionBounds.verify("proof.lean", targets)`. Pass options as the third
argument when needed. Each target is a `{module, function, arity}` tuple,
and the proof is checked independently against each distinct target.

For interactive checks, pass a `~LEAN` declaration as the `postlude:`
option. This example can be run in `iex -S mix` from the project root.

```elixir
# cspell:words fixpoint
import Lynx.Lean

{:module, SumDemo, beam, _} =
  defmodule SumDemo do
    @compile :debug_info

    def sum(0), do: 0
    def sum(n), do: sum(n - 1) + n
  end

ReductionBounds.verify([{SumDemo, :sum, 1}],
  beam_binaries: [beam],
  termination_suffixes: %{{SumDemo, :sum, 1} => ~LEAN"partial_fixpoint"},
  postlude: ~LEAN"""
  theorem sumZero : Elixir.SumDemo.«sum/1» (.integer 0) = .ok (.integer 0) := by
    rw [Elixir.SumDemo.«sum/1».eq_def]
    rfl
  """
)
```

The termination suffix lets Lean model recursion on inputs for which
the function may diverge. The theorem checks the return value for input zero.

## Planned approach

The initial scope is a subset of terminating Erlang and Elixir code running
in a single process on specified versions of Elixir and Erlang/OTP. The
analysis will combine reusable bounds for BEAM instructions and built-in
functions with rules for branches, calls, and bounded recursion. The runtime
model will account for built-in functions that can yield and resume, under
stated execution assumptions.

The library will take a function definition and input preconditions. Some
functions may also require annotations, such as size measures or recursion
invariants. Lynx integration is planned for expressing source-level
conditions, and Lean will check the derivation. The library will report
the resulting formula, its assumptions, and the applicable runtime
versions. It will distinguish bounds proved for the cost model from bounds
justified against ERTS reduction accounting and identify unsupported
operations or unresolved proof obligations.

## Symbolic list bounds

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

## Input limitations

The initial Lynx-based analysis requires Core Erlang for the target
function and any dependencies that Lynx needs to translate. When loading
a compiled Erlang or Elixir module, Lynx uses its BEAM debug information
to recover Core Erlang and translate the relevant functions to Lean.
This path requires a debug information backend that can provide Core
Erlang. BEAM files with stripped debug information fall outside the
initial scope, as do functions or dependencies that use constructs Lynx
cannot translate.
See [Lynx's module-loading implementation](https://github.com/josevalim/lynx/blob/d74890ac7a446d57b762d0e4fcd3c848146b2ff6/lib/lynx/translation.ex#L333-L385).

By default, verification resolves modules through readable `.beam` files on
the code path. For modules defined in IEx or with `Code.compile_string/1`,
retain the BEAM binaries returned by compilation and pass them to either verification form
using `beam_binaries: [beam]`. Include binaries for any dependencies that
exist only in memory. Each supplied binary must contain debug information
that Lynx can use to recover Core Erlang.

Lynx stops translation when a call returns to a module already on its
translation stack. Protocol dispatch can introduce such dependencies.
For example, translating the general enumerable clause of `Enum.map/2`
can reach Enumerable.File.Stream, whose implementation calls back into
`Enum.reduce/3`. Lynx can encounter that path while translating
`Enum.map/2` even when the intended inputs are lists. The resulting
`cyclic module call` diagnostic is reported before Lean checks the proof.
See [Lynx's cycle detection](https://github.com/josevalim/lynx/blob/d74890ac7a446d57b762d0e4fcd3c848146b2ff6/lib/lynx/translation.ex#L236-L270).

## Roadmap

- Use circular-buffer insertion to evaluate bounds for individual calls and
  sequences, including insertions that trigger list reversal.
- Use list membership and conditional reversal to test whether the same
  rules and previously established bounds can be reused across functions.
- Release an open-source prototype and document the supported operations,
  the annotations users need to supply, and how much of the derivation the
  library can automate.
- Investigate deriving reduction bounds directly from BEAM instructions,
  with the longer-term goal of accepting arbitrary BEAM modules, including
  binaries with stripped debug information. This would require an
  instruction-level model of execution and reduction accounting for the
  target ERTS version.

## License

Copyright 2026 University of Kitakyushu.

Licensed under the Apache License, Version 2.0. See [LICENSE.md](LICENSE.md).
