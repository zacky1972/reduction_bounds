# ReductionBounds

`reduction_bounds` is an experimental Elixir library for deriving symbolic
upper bounds on the number of reductions that BEAM charges for a function
call or a sequence of calls. The project is in early development.

A bound describes how the reduction count depends on inputs and their
preconditions, such as a maximum list length. A bound in reductions
expresses work in BEAM's scheduling units. Turning it into a bound on
elapsed time requires separate, platform-specific timing evidence.

## Lean prerequisites

For Lynx-based proof checking, install [Elan](https://github.com/leanprover/elan),
Lean's toolchain manager, and make sure `lake` is available on `PATH`.
Use the Lean version specified by Lynx's `lean-toolchain` file. The
[referenced Lynx revision](https://github.com/josevalim/lynx/blob/d74890ac7a446d57b762d0e4fcd3c848146b2ff6/lean-toolchain)
specifies Lean 4.35.0 (`leanprover/lean4:v4.35.0`).

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

The current `verify/2` and `verify/3` APIs require a readable `.beam` file
on the code path. Modules defined interactively in IEx or compiled
with `Code.compile_string/1` are outside this scope when they exist only
in memory. To verify such a module, compile it to a `.beam` file with
debug information and make the file available on the code path.

Lynx stops translation when a call returns to a module already on its
translation stack. Protocol dispatch can introduce such dependencies.
For example, translating the general enumerable clause of `Enum.map/2`
can reach `Enumerable.File.Stream`, whose implementation calls back into
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
