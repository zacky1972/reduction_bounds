# Verify Lean declarations

The verification API checks caller-supplied Lean declarations against
functions translated by Lynx. Separate APIs derive symbolic bounds for
supported fragments; see [the examples index](../examples.md).

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

See [proof scope and limitations](../proof.md#scope) for the distinction
between a checked model and concrete runtime behavior.

## Translation limitations

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
