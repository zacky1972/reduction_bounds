# ReductionBounds

`reduction_bounds` is an experimental Elixir library for deriving symbolic
upper bounds on the number of reductions that BEAM charges for a function
call or a sequence of calls. The project is in early development.

A bound describes how the reduction count depends on inputs and their
preconditions, such as a maximum list length. A bound in reductions
expresses work in BEAM's scheduling units. Turning it into a bound on
elapsed time requires separate, platform-specific timing evidence.

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

## Roadmap

- Use circular-buffer insertion to evaluate bounds for individual calls and
  sequences, including insertions that trigger list reversal.
- Use list membership and conditional reversal to test whether the same
  rules and previously established bounds can be reused across functions.
- Release an open-source prototype and document the supported operations,
  the annotations users need to supply, and how much of the derivation the
  library can automate.

## License

Copyright 2026 University of Kitakyushu.

Licensed under the Apache License, Version 2.0. See [LICENSE.md](LICENSE.md).
