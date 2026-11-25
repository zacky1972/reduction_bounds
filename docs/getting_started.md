# Getting Started

Use this guide to install ReductionBounds, check a first symbolic bound, and
choose a [Case Study](case_studies.md) for your program. The examples check
mathematical cost models in Lean; a successful check does not establish a
concrete BEAM reduction count or a real-time deadline.

## 1. Prepare the tools

Install Git, Elixir 1.20 or later in the 1.x series, a compatible Erlang/OTP,
and [Elan](https://github.com/leanprover/elan). Put Elan's `lean` and `lake`
commands on `PATH` (normally by adding `$HOME/.elan/bin`).

Choose one project layout.

### Work in this repository

```sh
git clone https://github.com/zacky1972/reduction_bounds.git
cd reduction_bounds
mix deps.get
cmp lean-toolchain deps/lynx/lean-toolchain
export ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)"
elan toolchain install "$ELAN_TOOLCHAIN"
lean --version
lake --version
mix compile
```

Keep the checked-out `mix.lock`; dependency updates are a separate maintenance
operation. If the two toolchain files disagree, resolve that checkout/dependency
mismatch using the [toolchain guide](toolchains.md) before proof checking.

### Use an existing or new Mix application

For a new application, first run `mix new bounds_demo` and `cd bounds_demo`.
Add this entry to `deps/0` in your application's `mix.exs`:

```elixir
{:reduction_bounds, github: "zacky1972/reduction_bounds", branch: "main"}
```

Then, from that application's root:

```sh
mix deps.get
export ELAN_TOOLCHAIN="$(cat deps/lynx/lean-toolchain)"
elan toolchain install "$ELAN_TOOLCHAIN"
lean --version
lake --version
mix compile
```

Set `ELAN_TOOLCHAIN` again in each new shell unless a matching project
`lean-toolchain` file selects it. Use the version required by the fetched Lynx
dependency; installing the newest Lean independently may be incompatible.
Repository test, benchmark and calibration commands later in these guides are
for the ReductionBounds checkout, not a consuming application's own test suite.

## 2. Check the constant case in IEx

Start from your prepared project root:

```sh
iex -S mix
```

Paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule FirstBound do
  @compile :debug_info
  def zero(), do: 0
end
""")
beams = Enum.map(compiled, &elem(&1, 1))
{:ok, bound} = ReductionBounds.infer_integer_cost_bound(
  {FirstBound, :zero, 0}, beam_binaries: beams)
bound.upper_bound
bound.result_size
Enum.map(bound.reports, & &1.status)
```

The final list should contain only `:ok` statuses. The bound is a symbolic
expression even though the returned value is zero: evaluating or returning a
constant can still have a charge in the cost model. No input domain is needed
for this zero-argument function. The first check can prepare shared Lean
artifacts and take longer than a later check.

To analyze a source file instead, follow the complete file-loading route in
[Constant and branch](case_studies.md#constant-and-branch). Compile the file
before starting IEx; readable BEAM files supply source evidence without
`beam_binaries`. For IEx-only modules, retain the compilation binaries as above.
Debug information is required in either route.

## 3. Read the guarantee before applying it

Check the returned formula together with the result's conditions and proof
scope. Fields differ by API; the [Case Studies](case_studies.md) show which to
inspect. In particular:

- A symbolic charge is an assumption about mathematical work. Naming a cost
  contract `:jit` does not establish applicability to a JIT runtime.
- Size ranges and call contracts constrain the executions covered by the bound.
  Reused evidence is checked again, with its assumptions retained.
- Protocol cost safety does not imply progress, actual reply delivery, source
  termination or elapsed-time bounds. Completion is a separate conditional claim.
- `verify/2,3` returns per-target results; inspect each one even when the outer
  result is `{:ok, results}`. The inference APIs report failed checks as errors.

See [proof scope](proof.md#scope) for trusted extraction, model correspondence
and unresolved runtime obligations.

## 4. Progress through the Case Studies

| Your next question | Continue with |
| --- | --- |
| How do branches and recursion compose? | [Constant/branch](case_studies.md#constant-and-branch), then [natural recursion](case_studies.md#natural-number-recursion) |
| How does input length affect work? | [Lists and conditional reversal](case_studies.md#list-traversal-and-conditional-reversal) |
| Can intermediate integers grow? | [Integer sizes and accumulators](case_studies.md#integer-sizes-calls-and-growing-accumulators) |
| Can a verified contract be reused? | [Contract comparison and transfer](case_studies.md#contract-comparison-and-bound-transfer) |
| What about buffers, maps or messages? | [Case Studies index](case_studies.md#choose-a-case) |

Each source case provides both compiled-file and IEx instructions. Built-in or
protocol-model cases instead show interactive calls and an equivalent script;
these do not claim to analyze an arbitrary user implementation.

## 5. Run repository checks and calibrate separately

In the ReductionBounds checkout, reproduce a selected group first:

```sh
mix test --only case_study --trace
```

For the ordinary full suite:

```sh
mix test
```

For machine-specific job/thread settings, use
[Test Performance Calibration](test_performance.md). Calibration runs multiple
complete suites and requires a clean committed checkout. Copying a fast-looking
setting or changing ExUnit's `max_cases` alone is not a calibration.

## Common setup problems

| Symptom | Check |
| --- | --- |
| `lean` or `lake` is unavailable | Elan installation and `PATH` in the shell running Mix |
| Lean version mismatch | `ELAN_TOOLCHAIN` and `deps/lynx/lean-toolchain` |
| Target source cannot be recovered | Compile with debug information; retain/pass binaries for in-memory modules and dependencies |
| Unsupported Core construct or translation cycle | Select a supported fragment; see [translation limitations](examples/verification.md#translation-limitations) |
| Proof timeout | Inspect the error and resource load; consult [job-budget diagnostics](job_budget.md). A timeout is not a checked bound |

The [examples index](examples.md) and [proof reference](proof.md) provide deeper
API and theorem details after the walkthrough.
