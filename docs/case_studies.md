<!-- cspell:words bigl bigr mathbb mathrm operatorname texttt -->
<!-- cspell:words erpc -->
# Case Studies

These cases develop symbolic cost bounds from small Elixir programs, following
constant evaluation, branches, recursion, traversal and Port clients in the
paper, then extending to the other public analysis workflows. Start with
[Getting Started](getting_started.md) for installation and your first check.

A checked bound is a theorem about a supported mathematical model under its
reported conditions. It is not a measured BEAM reduction count or a wall-clock
bound. Runtime cost correspondence, helper contracts and progress assumptions
must be assessed separately. See the [proof reference](proof.md) for exact scopes.

## Choose a case

| Case | Public workflow | Main result |
| --- | --- | --- |
| [Constant and branch](#constant-and-branch) | `infer_integer_cost_bound/2` | Local costs and a maximum over branches |
| [Natural-number recursion](#natural-number-recursion) | `infer_verified_bound/2` | Recurrence and model termination under call contracts |
| [List traversal and conditional reversal](#list-traversal-and-conditional-reversal) | `infer_search_bound/2`, `infer_list_bound/2`, `infer_list_call_bound/3` | Length-based bounds, value models and callee reuse |
| [Integer sizes, calls and growing accumulators](#integer-sizes-calls-and-growing-accumulators) | `infer_integer_sizes/2`, `infer_integer_cost_bound/2` | Input domains, intermediate widths and finite recursive derivations |
| [Contract comparison and bound transfer](#contract-comparison-and-bound-transfer) | `compare_cost_contracts/3`, `transfer_integer_bound/3` | Ordered contracts and rechecked bound reuse |
| [Variance and CRC kernels](#variance-and-crc-kernels) | `infer_integer_cost_bound/2` | Arithmetic and bitwise expressions |
| [Maps and structs](#maps-and-structs) | `infer_struct_bound/2` | Cost trees, normalization and value-agreement scope |
| [Periodic state transitions](#periodic-state-transitions) | `infer_periodic_bound/2` | Exact event count and repeated-step cost |
| [Ring-buffer insertions](#ring-buffer-insertions) | `infer_circular_buffer_bound/1`, `infer_circular_buffer_sequence_bound/1` | Rotation cost, exact sequence count and FIFO model |
| [Port protocol and source](#port-protocol-and-source) | `verify_port_model/3`, `infer_port_bound/3` | Participant cost safety and a helper-contracted source connection |
| [Single-attempt RPC](#single-attempt-rpc) | `verify_rpc_conditions/4`, `verify_rpc_model/4`, `infer_rpc_bound/3` | Mailbox matching, participant budgets and restricted source connection |
| [Caller-supplied Lean proofs](#caller-supplied-lean-proofs) | `verify/2`, `verify/3` | Value theorem for a translated target |

## File and IEx conventions

Run shell commands from a Mix project containing ReductionBounds, or from this
repository after setup. Each source case is self-contained. Start a fresh IEx session for each case
and choose **one** loading route:

- **File:** save the shown module(s) at the named `lib/` path, run `mix compile`,
  then `iex -S mix`. Set `beam_options = []` in that session. Compilation leaves
  readable BEAM files on the code path with debug information.
- **IEx:** start `iex -S mix` without creating the source file, and paste the
  complete `Code.compile_string/1` block shown for that case. It retains all
  in-memory BEAM binaries in `beam_options`.

Then run the common analysis block for that case in the same session. A file
existing on disk is insufficient unless it has been compiled. Modules defined
only in memory need `beam_binaries`, including in-memory dependencies. Avoid
loading both routes for the same module in one session. None of these examples
requires adding an example `.ex` file to this library's implementation.

In the API calls, `beam_options` supplies source evidence; other options supply
input/cost conditions. Do not replace input domains with the concrete values of
one test execution. Results retain their assumptions even after a Lean check.


## Read symbolic output as mathematics

The API returns expression trees so that formulas can be inspected. The
following notation is used throughout this page; `$U(T)$` evaluates a bound tree.
All charges and size/count parameters are nonnegative unless explicitly stated.

| Elixir output | Mathematical meaning |
| --- | --- |
| `{:add, left, right}` | `$U(\mathrm{left})+U(\mathrm{right})$` |
| `{:max, left, right}` | `$\max(U(\mathrm{left}),U(\mathrm{right}))$` |
| `{:mul, :n, step}` | `$n\,U(\mathrm{step})$` |
| `{:div, numerator, denominator}` | `$\lfloor U(\mathrm{numerator})/U(\mathrm{denominator})\rfloor$`, for a positive denominator |
| `{:sub, :n, 1}` in natural-count formulas | `$\max(n-1,0)$`; subtraction saturates at zero |
| `{:if_zero, :m, zero, positive}` | Choose the zero branch at `$m=0$`, otherwise the positive branch |
| `{:cost, operation, [w1, w2]}` | `$c_{\mathrm{operation}}(w_1,w_2)$`, a charge parameterized by sizes |
| `{:charge, clause, operation}` | `$c_{\mathrm{clause},\mathrm{operation}}$`, a symbolic charge local to that clause |
| `{:opaque_cost, id}` | `$o_{\mathrm{id}}$`, an explicit cost for an opaque path |

Sequential and alternative tree rules are

```math
U(\operatorname{seq}(T_1,T_2))=U(T_1)+U(T_2),\qquad
U(\operatorname{alt}(T_1,T_2))=\max(U(T_1),U(T_2)).
```

A theorem establishes `$C\leq U(T)$` under its conditions; it need not give the
exact cost `$C$`. By contrast, an exact event count is identified as such below.
A `result_size` constrains the returned value and is not a cost formula.
Numeric illustrations evaluate declared charges; they do not calibrate ERTS
reductions or CPU time. The rendered HTML uses KaTeX from a pinned CDN; loading
its math assets requires network access. Elixir, shell and Lean code blocks remain copyable.

## Constant and branch

The constant has no input. The branch admits integers from -4 through 4.
Sequential work is added; alternative paths use a maximum. The integer-size
parameters describe mathematical integer magnitudes, not a fixed machine word.

### File version

Save as `lib/case_studies/integer.ex` (create the directory first):

```elixir
defmodule CaseStudies.Integer do
  @compile :debug_info
  def zero(), do: 0
  def bump_if_nonnegative(x) do
    y = x + 1
    if x < 0, do: x, else: y
  end
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Integer do
  @compile :debug_info
  def zero(), do: 0
  def bump_if_nonnegative(x) do
    y = x + 1
    if x < 0, do: x, else: y
  end
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
alias ReductionBounds.IntegerSize
{:ok, constant} =
  ReductionBounds.infer_integer_cost_bound({CaseStudies.Integer, :zero, 0}, beam_options)
{:ok, branch} =
  ReductionBounds.infer_integer_cost_bound(
    {CaseStudies.Integer, :bump_if_nonnegative, 1},
    Keyword.merge(beam_options,
      input_sizes: [%IntegerSize{lower: -4, upper: 4, magnitude_bits: 3}]))
constant.upper_bound
branch.upper_bound
branch.result_size
branch.conditions
```


### Read the formulas

The constant's output is `{:cost, :value, [0, 0]}`. Let
`$v=c_{\mathrm{variable}}(0,0)$`, `$\ell=c_{\mathrm{value}}(0,0)$` and
`$b=c_{\mathrm{binding}}(0,0)$`. The displayed trees mean

```math
\begin{aligned}
B_{\mathrm{zero}} &= \ell,\\
B_{\mathrm{branch}} &=
  2v+\ell+b+c_{\mathrm{addition}}(3,1)+c_{\mathrm{comparison}}(3,0).
\end{aligned}
```

The addition uses a 3-bit magnitude bound for `x` and a 1-bit bound for
literal one. Comparison uses a 3-bit operand and zero's 0-bit bound. There
are two variable charges after simplifying `$\max(v,v)=v$`. The binding
charge pays for storing the intermediate. The input domain is
`$-4\leq x\leq4$`; the returned size description gives
`$-4\leq y\leq5$` and `$|y|<2^4$`. The numbers inside `:cost` are size
parameters, not measured costs. Returning zero does not force its cost to zero.


## Natural-number recursion

This unary natural-number model yields a zero equation and a successor
equation. `:previous` in the latter denotes the bound at the preceding input.
It is distinct from the finite input-range expansion of the integer-cost API.
Static external unary calls require `call_contracts` for result, cost and
normal-return assumptions; see the [execution model](proof.md#execution-soundness-for-unary-core-erlang-functions).

### File version

Save as `lib/case_studies/recursion.ex` (create the directory first):

```elixir
defmodule CaseStudies.Recursion do
  @compile :debug_info
  def sum(0), do: 0
  def sum(n), do: sum(n - 1) + n
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Recursion do
  @compile :debug_info
  def sum(0), do: 0
  def sum(n), do: sum(n - 1) + n
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
{:ok, bound} =
  ReductionBounds.infer_verified_bound({CaseStudies.Recursion, :sum, 1}, beam_options)
bound.precondition
bound.upper_bound.zero
bound.upper_bound.successor
bound.termination
```


### Read the recurrence

Write `$c_{\mathrm{branch}}$`, `$c_{\mathrm{bind}}$`,
`$c_{\mathrm{subtract}}$`, `$c_{\mathrm{recursive\ call}}$` and
`$c_{\mathrm{add}}$` for the returned `{:charge, operation}` leaves. Then

```math
\begin{aligned}
B(0)&=c_{\mathrm{branch}},\\
K&=c_{\mathrm{branch}}+2c_{\mathrm{bind}}+c_{\mathrm{subtract}}
    +c_{\mathrm{recursive\ call}}+c_{\mathrm{add}},\\
B(n+1)&=K+B(n),\\
B(n)&=c_{\mathrm{branch}}+nK \qquad(n\in\mathbb N).
\end{aligned}
```

`:previous` is `$B(n)$` in the successor equation. Subtraction constructs the
recursive argument, the two bindings retain intermediate results, and addition
combines the recursive result with the current input. The result is a bound
on modeled cost, not the returned sum `$n(n+1)/2$`. These charges are independent
of operand widths in this API; size-dependent integer costs use another model.


## List traversal and conditional reversal

For proper integer lists of length at most `n`, the traversal has a base plus
at most `n` continuing steps. `refined_upper_bound` distinguishes an empty-list
ending from a nonempty early stop. The wrapper adds its own cost to the checked
callee bound. Conditional reversal composes membership with the shared reversal
contract; ring-buffer insertion reuses that reversal contract too.
`value_model` identifies recognized value correspondence; a missing model does
not claim it. A custom `input_contract` can supply a precondition, tail
invariant and size measure; see [input contracts](proof.md#input-contracts-and-forwarding-calls).

### File version

Save as `lib/case_studies/lists.ex` (create the directory first):

```elixir
defmodule CaseStudies.Lists do
  @compile :debug_info
  def contains(_key, []), do: false
  def contains(key, [head | _]) when head === key, do: true
  def contains(key, [_ | tail]), do: contains(key, tail)
  def list_length([]), do: 0
  def list_length([_ | tail]), do: 1 + list_length(tail)
  def forward_length(xs), do: list_length(xs)
  def reverse_on_hit(key, xs) do
    if :lists.member(key, xs), do: :lists.reverse(xs, []), else: xs
  end
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Lists do
  @compile :debug_info
  def contains(_key, []), do: false
  def contains(key, [head | _]) when head === key, do: true
  def contains(key, [_ | tail]), do: contains(key, tail)
  def list_length([]), do: 0
  def list_length([_ | tail]), do: 1 + list_length(tail)
  def forward_length(xs), do: list_length(xs)
  def reverse_on_hit(key, xs) do
    if :lists.member(key, xs), do: :lists.reverse(xs, []), else: xs
  end
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
{:ok, search} =
  ReductionBounds.infer_search_bound({CaseStudies.Lists, :contains, 2}, beam_options)
{:ok, length} =
  ReductionBounds.infer_list_bound({CaseStudies.Lists, :list_length, 1}, beam_options)
{:ok, wrapper} = ReductionBounds.infer_list_call_bound(
  {CaseStudies.Lists, :forward_length, 1},
  {CaseStudies.Lists, :list_length, 1}, beam_options)
{:ok, conditional} =
  ReductionBounds.infer_list_bound({CaseStudies.Lists, :reverse_on_hit, 2}, beam_options)
{:ok, member} = ReductionBounds.infer_list_bound({:lists, :member, 2})
{:ok, reverse} = ReductionBounds.infer_list_bound({:lists, :reverse, 2})
search.upper_bound
length.refined_upper_bound
wrapper.upper_bound
conditional.upper_bound
conditional.value_model
member.upper_bound
reverse.upper_bound
```


### Read the traversal and composition bounds

The search output `{:add, {:max, :c_empty, :c_hit}, {:mul, :n, :c_step}}` means

```math
B_{\mathrm{search}}(n)=\max(c_{\mathrm{empty}},c_{\mathrm{hit}})
                       +n c_{\mathrm{step}}.
```

Here `$n$` bounds the initial length. The step charge pays for continuing to the
tail; the final charge pays for empty-list or head-match termination. For length,
let `$L_0=c_{0,\mathrm{dispatch}}+c_{0,\mathrm{value}}$` and
`$L_s=c_{1,\mathrm{dispatch}}+c_{1,\mathrm{recursive\ call}}+c_{1,\mathrm{addition}}$`. Then

```math
B_{\mathrm{length}}(n)=L_0+nL_s,\qquad
B_{\mathrm{wrapper}}(n)=c_{\mathrm{caller}}+B_{\mathrm{length}}(n).
```

Clause indices in `{:charge, index, operation}` are zero-based. For built-in
membership, write `$E,H,S$` for empty, hit and continuing-step charges. Its
refined bound is

```math
M(n)=\begin{cases}
E & n=0,\\
\max(E+nS,\ H+(n-1)S) & n>0.
\end{cases}
```

A successful head match needs a nonempty list, so at most `$n-1$` earlier
continuations precede it. A miss can visit all `$n$` cells and then the empty
list. Reversal has `$R(n)=R_0+nR_s$` for its own base and step charges.
The conditional-reversal tree therefore means

```math
B_{\mathrm{conditional}}(n)=
\max\bigl(M(n)+B_{\mathrm{hit}}+R(n),\ M(n)+B_{\mathrm{miss}}\bigr).
```

Membership is paid on both paths; reversal is paid only on a hit. A
`{:call_bound, target, expression}` identifies the callee and encloses its bound;
it does not add an extra unspecified constant. `:branch_cost` leaves record
the local branch work separately.


## Integer sizes, calls and growing accumulators

Size inference alone derives ranges and intermediate magnitude widths, not a
cost bound. Integer-cost inference composes nondecreasing size-dependent charges.
The accumulator may grow while the counter decreases. A reused callee's evidence
is checked again; supplying its result map is not a substitute for replay.
`recursive_invariant` can constrain both recursive arguments. Exhausting
`max_unfolding` or `max_nodes` is an error, not proof of termination. See the
[integer rules](proof.md#integer-sizes-connected-to-symbolic-costs).

### File version

Save as `lib/case_studies/sizes.ex` (create the directory first):

```elixir
defmodule CaseStudies.Sizes do
  @compile :debug_info
  def update(x) do
    y = x * 3
    if y < 0, do: y - 1, else: y + 1
  end
  def sum(counter, accumulator) do
    if counter > 0,
      do: sum(counter - 1, accumulator + counter),
      else: accumulator
  end
  def triple(x), do: x * 3
  def caller(x), do: __MODULE__.triple(x) + 1
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Sizes do
  @compile :debug_info
  def update(x) do
    y = x * 3
    if y < 0, do: y - 1, else: y + 1
  end
  def sum(counter, accumulator) do
    if counter > 0,
      do: sum(counter - 1, accumulator + counter),
      else: accumulator
  end
  def triple(x), do: x * 3
  def caller(x), do: __MODULE__.triple(x) + 1
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
alias ReductionBounds.IntegerSize
input = %IntegerSize{lower: -2, upper: 4, magnitude_bits: 3}
{:ok, sizes} = ReductionBounds.infer_integer_sizes(
  {CaseStudies.Sizes, :update, 1}, Keyword.merge(beam_options, input_sizes: [input]))
{:ok, sum} = ReductionBounds.infer_integer_cost_bound(
  {CaseStudies.Sizes, :sum, 2}, Keyword.merge(beam_options,
    input_sizes: [%IntegerSize{lower: 0, upper: 4, magnitude_bits: 3},
                  IntegerSize.from_integer(0)]))
{:ok, callee} = ReductionBounds.infer_integer_cost_bound(
  {CaseStudies.Sizes, :triple, 1}, Keyword.merge(beam_options, input_sizes: [input]))
{:ok, caller} = ReductionBounds.infer_integer_cost_bound(
  {CaseStudies.Sizes, :caller, 1}, Keyword.merge(beam_options,
    input_sizes: [input], call_contracts: %{{CaseStudies.Sizes, :triple, 1} => callee}))
sizes.result_size
sizes.intermediates
sizes.unresolved_sizes
sum.conditions.inferred_recursive_inputs
sum.upper_bound
caller.upper_bound
```


### Read sizes and the expanded cost tree

For `update/1`, the returned size description is

```math
-7\leq y\leq13,\qquad |y|<2^6.
```

The interval and magnitude bound are simultaneous conditions; the width is a
conservative propagated bound, not the smallest width implied by the interval.
For the given recursive inputs, `sum.result_size` describes
`$0\leq r\leq10$` and `$|r|<2^7$`.

The large `sum.upper_bound` is a finite tree. Its addition nodes accumulate
work at successive recursion levels; its maximum nodes include the possible
stopping paths. In particular, do not multiply one initial-width step charge
by four: later accumulator/intermediate widths have changed. In the common
notation below, this output is `$B_{\mathrm{sum}}=U(T_{\mathrm{sum}})$`.

For `triple/1`, the much smaller tree is

```math
B_{\mathrm{triple}}=
 c_{\mathrm{variable}}(0,0)+c_{\mathrm{value}}(0,0)
 +c_{\mathrm{multiplication}}(3,2).
```

The second width is two because the multiplier is three. `caller.upper_bound`
contains a `:call_bound` leaf carrying the rechecked callee formula, plus
caller argument evaluation, call, literal and addition work. The same input
domain must be covered by the callee contract. Result ranges describe values;
none of these widths is itself a number of reductions.


## Contract comparison and bound transfer

This case defines its own unary target. No earlier case or session state is
required. Comparison alone selects no source target and needs no BEAM binaries.

### File version

Save as `lib/case_studies/transfer.ex` (create the directory first):

```elixir
defmodule CaseStudies.Transfer do
  @compile :debug_info
  def triple(x), do: x * 3
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Transfer do
  @compile :debug_info
  def triple(x), do: x * 3
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
alias ReductionBounds.{CostContract, IntegerSize}
functions_b = Map.new(CostContract.operations(), &{&1, {:add, 2, :left}})
functions_a = Map.new(CostContract.operations(), &{&1, {:add, 1, :left}})
{:ok, b} = CostContract.new(id: :source, functions: functions_b)
{:ok, a} = CostContract.new(id: :destination, functions: functions_a)
{:ok, original} = ReductionBounds.infer_integer_cost_bound(
  {CaseStudies.Transfer, :triple, 1}, Keyword.merge(beam_options,
    input_sizes: [%IntegerSize{lower: -2, upper: 4, magnitude_bits: 3}],
    cost_contract: b))
{:ok, comparison} = ReductionBounds.compare_cost_contracts(a, b,
  budget: original.upper_bound)
{:ok, transferred} = ReductionBounds.transfer_integer_bound(original, a, beam_options)
comparison.budget_values
transferred.upper_bound_contract
#=> :source
transferred.upper_bound_value
transferred.verification_scope
transferred.checked_theorems
```

Comparison runs **smaller to larger**. Transfer rechecks the source bound under
B, checks A <= B, and retains the bound evaluated under B for A executions.
Contract names do not establish JIT/interpreter applicability. Contracted calls
also require external-model correspondence; see [comparison and transfer](examples/cost_contracts.md).


### Read ordering and the transferred number

For every registered operation, the declarations in this example are

```math
c_A(w_1,w_2)=1+w_1\leq2+w_1=c_B(w_1,w_2).
```

`triple/1` evaluates a variable, a literal and multiplication at widths `$(3,2)$`.
Consequently `comparison.budget_values` is `%{smaller: 6, larger: 9}`:

```math
U_A=1+1+(1+3)=6,\qquad U_B=2+2+(2+3)=9.
```

Transfer retains `$U_B=9$` as a valid upper bound for destination-A executions:

```math
\operatorname{value}_A=\operatorname{value}_B,\qquad
C_A\leq C_B\leq U_B=9.
```

This explains why `transferred.upper_bound_contract` remains `:source` and
`upper_bound_value` is nine rather than six. These numbers are evaluations of
declared mathematical charges, not experimentally calibrated runtime costs.


## Variance and CRC kernels

The variance numerator is an integer arithmetic kernel; it does not include
floating-point division or square root. The CRC table lookup is outside the
analyzed function: its result is an input with an explicit domain. These are
not whole-library proofs. Other directions, masks and indices are reproduced by
`REDUCTION_BOUNDS_REPORT=1 mix test --only cost_contract_workflow --trace`
in the repository.

### File version

Save as `lib/case_studies/kernels.ex` (create the directory first):

```elixir
defmodule CaseStudies.Kernels do
  @compile :debug_info
  def variance_numerator(sum, sum_squares, count) do
    count * sum_squares - sum * sum
  end
  def crc64_update(crc, table_entry) do
    shifted = Bitwise.bsl(crc, 8)
    mixed = Bitwise.bxor(shifted, table_entry)
    Bitwise.band(mixed, 0xFFFFFFFFFFFFFFFF)
  end
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Kernels do
  @compile :debug_info
  def variance_numerator(sum, sum_squares, count) do
    count * sum_squares - sum * sum
  end
  def crc64_update(crc, table_entry) do
    shifted = Bitwise.bsl(crc, 8)
    mixed = Bitwise.bxor(shifted, table_entry)
    Bitwise.band(mixed, 0xFFFFFFFFFFFFFFFF)
  end
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
alias ReductionBounds.IntegerSize
{:ok, variance} = ReductionBounds.infer_integer_cost_bound(
  {CaseStudies.Kernels, :variance_numerator, 3}, Keyword.merge(beam_options,
    input_sizes: [%IntegerSize{lower: 0, upper: 3, magnitude_bits: 2},
                  %IntegerSize{lower: 0, upper: 9, magnitude_bits: 4},
                  %IntegerSize{lower: 0, upper: 3, magnitude_bits: 2}]))
{:ok, crc} = ReductionBounds.infer_integer_cost_bound(
  {CaseStudies.Kernels, :crc64_update, 2}, Keyword.merge(beam_options,
    input_sizes: [%IntegerSize{lower: 0, upper: 255, magnitude_bits: 8},
                  %IntegerSize{lower: 0, upper: 255, magnitude_bits: 8}]))
variance.result_size
variance.upper_bound
crc.intermediates
crc.upper_bound
```


### Read intermediate-width charges

Let `$v=c_{\mathrm{variable}}(0,0)$` and
`$b=c_{\mathrm{binding}}(0,0)$`. The variance numerator's returned cost tree is

```math
B_{\mathrm{variance}}=6v+2b
 +c_{\mathrm{multiplication}}(2,4)
 +c_{\mathrm{multiplication}}(2,2)
 +c_{\mathrm{subtraction}}(6,4).
```

The two product widths are six and four; subtraction is charged at those
widths even if the final result is small. For the supplied independent domains,
the returned value range is `$[-9,27]$` with a conservative magnitude bound of
seven. Independent domains do not assume that the inputs actually came from
a common set of samples.

The CRC tree means

```math
B_{\mathrm{CRC}}=4v+2b+c_{\mathrm{shift\ left}}(8,8)
 +c_{\mathrm{xor}}(16,8)+c_{\mathrm{mask}}(17,64).
```

For shift-left, the second parameter is the shift amount, not the width of
that amount. For masking, it is the retained bit count. The shifted
intermediate has a 16-bit bound, signed XOR conservatively yields 17 bits,
and the mask bounds the result by `$0\leq r\leq2^{64}-1$`.
IEx may print the parameter list `[8, 8]` as a character list; it still denotes
two integer size parameters. The expression is a cost formula, not the CRC value.


## Maps and structs

The unguarded read checks value agreement with the reified source and bounds
the original operations. Guarded debit retains opaque paths and their symbolic
costs; its successful cost check does not upgrade value agreement to checked.
See [map and struct proofs](proof.md#map-and-struct-operations).

### File version

Save as `lib/case_studies/counter.ex` (create the directory first):

```elixir
defmodule CaseStudies.Counter do
  @compile :debug_info
  defstruct balance: 0, limit: 0
  def read_checked(%__MODULE__{balance: _} = counter), do: counter.balance
  def debit(%__MODULE__{balance: balance} = counter, amount)
      when is_integer(amount) and amount >= 0 and balance >= amount do
    %{counter | balance: balance - amount}
  end
  def debit(%__MODULE__{} = counter, _amount), do: counter
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Counter do
  @compile :debug_info
  defstruct balance: 0, limit: 0
  def read_checked(%__MODULE__{balance: _} = counter), do: counter.balance
  def debit(%__MODULE__{balance: balance} = counter, amount)
      when is_integer(amount) and amount >= 0 and balance >= amount do
    %{counter | balance: balance - amount}
  end
  def debit(%__MODULE__{} = counter, _amount), do: counter
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
{:ok, read} =
  ReductionBounds.infer_struct_bound({CaseStudies.Counter, :read_checked, 1}, beam_options)
{:ok, debit} =
  ReductionBounds.infer_struct_bound({CaseStudies.Counter, :debit, 2}, beam_options)
read.value_agreement
#=> :checked
read.normalization
read.upper_bound
debit.value_agreement
#=> :unsupported
debit.opaque_paths
debit.upper_bound
```


### Read the tree and opaque terms

Let `$m=c_{\mathrm{map\ match}}$`, `$b=c_{\mathrm{bind}}$`, and let
`$o_0,o_1$` name `{:opaque_cost, "fallback:0"}` and
`{:opaque_cost, "fallback:1"}`. The unguarded read's tree means

```math
B_{\mathrm{read}}=m+\max\bigl(b+m+\max(0,o_0),\ o_1\bigr).
```

The leading match always runs. The maximum retains successful and fallback
paths. A zero leaf is zero modeled work at that point; an opaque leaf is a
separately supplied symbolic cost, not free or proved unreachable work.

The larger debit tree is evaluated by the same `$U$` rules: sum operations on
one path and take a maximum over alternatives. It retains integer tests,
comparisons, subtraction, map checks, updates and opaque fallbacks. Do not
replace it by just the subtraction cost. A checked unguarded value-agreement
result and a guarded `:unsupported` result keep the distinct scopes shown above.


## Periodic state transitions

For period at least 2 and initial pending count below the period, `n` calls
emit exactly `$\lfloor(a+2n)/m\rfloor$` events. The cost is `$nc$` plus
that count times the event surcharge. Reset must retain the remainder;
resetting to zero after overshooting is a different transition. A
`periodic_contract` may add a Lean-checked invariant and measure; see the
[shared transition rule](proof.md#fixed-progress-and-periodic-resets).

### File version

Save as `lib/case_studies/batcher.ex` (create the directory first):

```elixir
defmodule CaseStudies.Batcher do
  @compile :debug_info
  def enqueue_pair(pending, period) do
    advanced = pending + 2
    if advanced >= period,
      do: {advanced - period, true},
      else: {advanced, false}
  end
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.Batcher do
  @compile :debug_info
  def enqueue_pair(pending, period) do
    advanced = pending + 2
    if advanced >= period,
      do: {advanced - period, true},
      else: {advanced, false}
  end
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
{:ok, bound} = ReductionBounds.infer_periodic_bound(
  {CaseStudies.Batcher, :enqueue_pair, 2}, beam_options)
bound.stride
#=> 2
bound.event_count
bound.upper_bound
bound.conditions
```


### Read the quotient and surcharge

Let `$a$` be the initial pending count, `$m$` the period, `$n$` the number of calls,
`$c$` the fixed per-call bound, and `$r$` the event surcharge. The output means

```math
q(a,m,n)=\left\lfloor\frac{a+2n}{m}\right\rfloor,\qquad
B(a,m,n)=nc+q(a,m,n)r,
\qquad 0\leq a<m,\quad m\geq2.
```

For example, `$a=1,m=4,n=5$` gives `$q=2$`, so the bound is `$5c+2r$` and
final pending count is one. The quotient counts events; the second expression
bounds cost. In this profile the quotient is exact, while the charge bounds
can be conservative. Setting `$n=0$` gives no events and no call cost.


## Ring-buffer insertions

These APIs recognize the supported `CircularBuffer` dependency and reuse the
list-reversal rule. There is no user target to redefine in IEx. In this
repository the dependency is test-only, so use the test environment:

```sh
MIX_ENV=test mix deps.get
MIX_ENV=test mix compile
MIX_ENV=test iex -S mix
```

In a consuming project, add the same dependency to `deps/0` (or to the test
environment used here):

```elixir
{:circular_buffer, git: "https://github.com/elixir-toniq/circular_buffer.git", tag: "v1.1.0"}
```

**IEx version:** paste these calls into that shell:

```elixir
{:ok, insertion} = ReductionBounds.infer_circular_buffer_bound()
{:ok, sequence} = ReductionBounds.infer_circular_buffer_sequence_bound()
insertion.upper_bound
sequence.rotation_count
sequence.upper_bound
```

**File version:** save those same calls to `ring_buffer_case.exs` outside `lib/`,
append `IO.inspect(sequence, limit: :infinity)`, and run:

```sh
MIX_ENV=test mix run ring_buffer_case.exs
```

For positive capacity `m`, the sequence API starts at `CircularBuffer.new/1`
and gives `$\lfloor\max(n-1,0)/m\rfloor$` rotations. At capacity zero there are no
rotations and the zero-capacity insertion cost applies. The underlying Lean
state theorem also covers valid nonempty initial states. FIFO agreement is a
state-model theorem; correspondence of all concrete buffer source clauses to
that state model remains a separate obligation. See [one insertion](proof.md#one-circularbuffer-insertion)
and [sequences and FIFO contents](proof.md#consecutive-circularbuffer-insertions).


### Read single-insertion and sequence bounds

For one insertion, let `$C_c,C_f,C_r,C_0$` denote the local consume, fill,
rotation and zero-capacity path charges. Let `$R(k)$` be the list-reversal
bound on at most `$k$` elements, and `$C_e$` its `Enum.reverse/1` wrapper charge.
The returned maximum bounds

```math
B_{\mathrm{insert}}(k)=
\max\bigl(C_c,\ C_f,\ C_r+C_e+R(k),\ C_0\bigr).
```

For the sequence API's empty initializer, the rotation-count output is

```math
q(m,n)=\begin{cases}
0 & m=0,\\
\left\lfloor\dfrac{\max(n-1,0)}{m}\right\rfloor & m>0.
\end{cases}
```

If `$c$` bounds local positive-capacity work per insertion and `$r(m)$` is the
rotation surcharge (including reversal), then

```math
B_{\mathrm{sequence}}(m,n)=\begin{cases}
nC_0 & m=0,\\
nc+q(m,n)r(m) & m>0.
\end{cases}
```

At `$m=4,n=9$`, there are two rotations, so the positive-capacity bound is
`$9c+2r(4)$`. The first rotation is on insertion five, after filling capacity
four; it is not charged on insertion four. The empty run has cost zero.
For a valid general state with initial newer-list length `$a_0$`, the underlying
state theorem instead uses
`$q=\lfloor\max(a_0+n-1,0)/m\rfloor$` for `$m>0$`; the public sequence example
specializes to `$a_0=0$`.


## Port protocol and source

A Port-size profile needs independent request, response and unrelated-message
bounds, plus aggregate count caps. These expressions declare symbolic event
costs; no external program is launched by verification.

**IEx model:** start `iex -S mix` and paste this setup and check:

```elixir
alias ReductionBounds.{PortProtocol, ProtocolConditions, ProtocolCost, ProtocolSize}

{:ok, conditions} = PortProtocol.conditions(
  data_bounds: Map.new([:request, :response, :message], fn slot ->
    {slot, %ProtocolSize{bytes: 8, structure: 16}}
  end),
  count_bounds: %{
    total_events: 30, submission_attempts: 4, submission_events: 8,
    resumptions: 3, retries: 3, receive_inspections: 8
  }
)

rules = for {{_, event} = context, rule} <- conditions.rules,
            elem(conditions.contract.events[event], 0) != nil, into: %{} do
  cost = Enum.reduce(rule.data, {:charge, :event_work}, fn slot, rest ->
    {:add, rest, {:add, {:data, slot, :bytes}, {:data, slot, :structure}}}
  end)
  {context, %{counter: List.first(rule.counts) || :total_events, cost: cost}}
end
{:ok, profile} = ProtocolCost.new(conditions, rules)

names = [:prepare, :submit_accepted, :response_arrived, :receive_response, :decode]
{:ok, observation} = ProtocolConditions.observe(%{request: [], response: [], message: []})
observations = Map.new(Enum.with_index(names), fn {_, index} -> {index, observation} end)
{:ok, model} = ReductionBounds.verify_port_model(profile, names, observations: observations)
model.upper_bounds
model.completion
model.verification_scope
```

**File model:** save that entire block as `port_model_case.exs` outside `lib/`,
append `IO.inspect(model, limit: :infinity)`, and run `mix run port_model_case.exs`.
No BEAM target is selected by this model-only API. Missing progress leaves the
model cost bound checked while completion remains unestablished. The
[Port guide](examples/ports.md#request-a-conditional-completion-theorem) shows
how to request termination or success under universal progress assumptions.


### Read the participant budget

For participant `$p$`, the general rule groups alternative event rules under
count caps:

```math
B_p=\sum_k N_k\max_{g\in G_{p,k}}c_g(W_g).
```

`$N_k$` is a declared count cap; `$G_{p,k}$` contains that participant's rules
assigned to that counter; `$W_g$` supplies the rule's independent size caps.
The maximum covers every rule sharing one counter. Different counter groups
are added, rather than assuming every event follows the success trace.

Here each size-dependent event charge is `$c_e+8+16=c_e+24$`, where `$c_e$`
is `{:charge, :event_work}`. The profile's grouped formula simplifies to

```math
\begin{aligned}
B_{\mathrm{caller}}&=46(c_e+24)+6c_e\\
                  &=52c_e+1104.
\end{aligned}
```

The coefficients 46 and 6 come from the declared counter groups, not from the
five events in `names`. For the illustrative interpretation `$c_e=1$`, the bound
is 1156 symbolic units. This is not a measurement or a bound on external-program
work. Waiting carries no active-work charge, but repeated active inspection does.


## Port source client

This case creates its own `profile` in the analysis block below. Both
modules are compiled in either route; helper bodies are provided for a concrete
source example, but their implementations are not established by this proof.
Do not call `request/2` merely to verify it. The source guarantee concerns finite
normally returning executions under helper contracts. It does not establish
native receive semantics, arbitrary unfinished source prefixes, source totality,
or concrete runtime costs.

### File version

Save as `lib/case_studies/port_client.ex` (create the directory first):

```elixir
defmodule CaseStudies.PortHelpers do
  @compile :debug_info
  def prepare(payload), do: payload
  def await_reply(port) do
    receive do
      {^port, {:data, payload}} -> {:data, payload}
      {^port, :closed} -> :closed
    after
      1_000 -> :timeout
    end
  end
  def decode(payload), do: payload
end

defmodule CaseStudies.PortClient do
  @compile :debug_info
  alias CaseStudies.PortHelpers, as: Helpers
  def request(port, input) do
    prepared = Helpers.prepare(input)
    case :erlang.port_command(port, prepared, [:nosuspend]) do
      true ->
        case Helpers.await_reply(port) do
          {:data, data} -> Helpers.decode(data)
          :closed -> :closed
          :timeout -> :timeout
        end
      false -> :rejected
    end
  end
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.PortHelpers do
  @compile :debug_info
  def prepare(payload), do: payload
  def await_reply(port) do
    receive do
      {^port, {:data, payload}} -> {:data, payload}
      {^port, :closed} -> :closed
    after
      1_000 -> :timeout
    end
  end
  def decode(payload), do: payload
end

defmodule CaseStudies.PortClient do
  @compile :debug_info
  alias CaseStudies.PortHelpers, as: Helpers
  def request(port, input) do
    prepared = Helpers.prepare(input)
    case :erlang.port_command(port, prepared, [:nosuspend]) do
      true ->
        case Helpers.await_reply(port) do
          {:data, data} -> Helpers.decode(data)
          :closed -> :closed
          :timeout -> :timeout
        end
      false -> :rejected
    end
  end
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
alias ReductionBounds.{PortProtocol, ProtocolCost, ProtocolSize}

{:ok, conditions} = PortProtocol.conditions(
  data_bounds: Map.new([:request, :response, :message], fn slot ->
    {slot, %ProtocolSize{bytes: 8, structure: 16}}
  end),
  count_bounds: %{
    total_events: 30, submission_attempts: 4, submission_events: 8,
    resumptions: 3, retries: 3, receive_inspections: 8
  }
)

rules = for {{_, event} = context, rule} <- conditions.rules,
            elem(conditions.contract.events[event], 0) != nil, into: %{} do
  cost = Enum.reduce(rule.data, {:charge, :event_work}, fn slot, rest ->
    {:add, rest, {:add, {:data, slot, :bytes}, {:data, slot, :structure}}}
  end)
  {context, %{counter: List.first(rule.counts) || :total_events, cost: cost}}
end
{:ok, profile} = ProtocolCost.new(conditions, rules)
{:ok, source} = ReductionBounds.infer_port_bound(
  {CaseStudies.PortClient, :request, 2}, profile, Keyword.merge(beam_options,
    calls: %{prepare: {CaseStudies.PortHelpers, :prepare, 1},
             reply: {CaseStudies.PortHelpers, :await_reply, 1},
             decode: {CaseStudies.PortHelpers, :decode, 1}}))
source.source_correspondence
source.upper_bounds
source.completion
source.verification_scope
```


### Read local work plus protocol work

The recognized client has a local source-node bound of 25. With `$c_s$` denoting
`{:charge, :source_node}`, its caller formula is

```math
B_{\mathrm{Port,source}}=25c_s+B_{\mathrm{caller}}
                       =25c_s+52c_e+1104.
```

At `$c_s=c_e=1$`, this evaluates to 1181. Local source-node work and protocol/helper
work must have compatible, disjoint accounting; the formula must not charge the
same operation twice. Helper correctness and source totality do not follow from
this numeric evaluation.


## Single-attempt RPC

This is ordinary same-node request/response, not the `rpc` or `erpc` module.
There is one attempt, one connected receive and at most one server invocation.

**IEx model:** start `iex -S mix` and paste:

```elixir
alias ReductionBounds.{Mailbox, RpcConditions, RpcCost, RpcProtocol, RpcServerContract, RpcTerm}
alias ReductionBounds.IntegerSize
cap = %RpcTerm.Size{nodes: 100, bytes: 32, integer_bits: 256}
{:ok, session} = RpcProtocol.new(7)
request = {:tuple3, {:atom, "request"}, {:ref, 7}, {:integer, 5}}
{:ok, conditions} = RpcConditions.new(session, request,
  request_size: cap, response_size: cap, message_size: cap,
  limits: Map.new(Mailbox.counters(), &{&1, 100}),
  protocol_limits: %{events: 100, client_sends: 1, server_sends: 1,
                     response_handlers: 1, retries: 0}, timeout: 0)
frame = %{message_size: cap, reply_size: cap, initial_messages: 10,
          arrivals: 10, inspections: 20, pattern_attempts: 20, guard_attempts: 20}
{:ok, server} = RpcServerContract.assume({CaseStudies.RpcHandler, :handle, 1},
  %IntegerSize{lower: 0, upper: 10, magnitude_bits: 4}, 30, frame)
rates = Map.new(RpcCost.operations() -- [:handle_request], fn op ->
  {op, %{cost_unit: if(RpcCost.owner(op) == :client, do: :client_work, else: :server_work),
         upper_bound: 2}}
end)
{:ok, cost_profile} = RpcCost.new(conditions, rates, server,
  initial_messages: 10, server_calls: 1)
reply = {:tuple3, {:atom, "reply"}, {:ref, 7}, {:integer, 9}}
timeline = [{:protocol, :prepare}, {:protocol, :send_request}, :begin_receive] ++
  Enum.map([:request_arrived, :receive_request, :handle_request, :send_reply],
    &{:protocol, &1}) ++ [{:arrive, reply}, :inspect, {:protocol, :process_reply}]

{:ok, checked_conditions} = ReductionBounds.verify_rpc_conditions(conditions, [], timeline)
{:ok, model} = ReductionBounds.verify_rpc_model(cost_profile, [], timeline,
  completion: [goal: :success,
    progress: [:client_progress, :request_progress, :server_progress,
               :response_progress, :no_failure_outcomes]])
checked_conditions.lean_status
model.upper_bounds
model.server_contract.status
#=> :assumed
model.completion.theorem_status
#=> :checked_under_assumptions
model.completion.actual_completion
#=> :not_established
```

**File model:** save the entire block to `rpc_model_case.exs` outside `lib/`,
append `IO.inspect(model, limit: :infinity)`, and run `mix run rpc_model_case.exs`.
The assumed handler MFA is a contract identifier; verification does not invoke
it or prove its implementation. Conditions-only verification does not claim a
cost bound. Completion requires progress over every admitted continuation,
not merely the supplied success timeline. Independent client/server units are
kept separate. See [handler replay](examples/rpc_cost.md#assumed-versus-replayed-server-handlers)
for composing a checked unary integer handler instead of an assumption.


### Read separate client and server numbers

The participant rule is a sum over owned operations:

```math
B_p=\sum_{o:\operatorname{owner}(o)=p}N_o r_o.
```

`$N_o$` is the operation cap and `$r_o$` its declared per-occurrence envelope.
The profile above assigns two to each non-handler operation, with an assumed
handler cost of 30. Its public result is

```math
B_{\mathrm{client}}=1210\ \text{client-work units},\qquad
B_{\mathrm{server}}=232\ \text{server-work units}.
```

These are sums of declared count caps times rates, including conservative
allowances for alternatives not seen in the supplied success timeline.
For the server, the generated caps give `$100\cdot2+1\cdot2+1\cdot30=232$`.
The units remain separate; `$1210+232$` is not a client reduction bound.
The value 30 stays an assumption even when protocol proofs succeed.

With mailbox action cap `$L$`, the separate completion argument uses
`$\rho=12R+p$` with `$R$` remaining actions and `$0\leq p\leq11$`, giving
at most `$11+12L$` active timeline items under the model. That is a proof rank,
not an elapsed-time bound or an additional cost charge.


## RPC source client

This case creates its own `cost_profile` in the analysis block below.
The supplied request fixes
the reified source input association; this is not analysis of all equally sized
requests. Native source receive and helper-body correctness are not proved.
Neither model completion nor a checked handler establishes source totality or
real reply delivery. Retries, duplicate execution, monitored source clients,
multiplexing, distributed traffic and receive optimizations remain unsupported.
See the [source boundary](examples/rpc_source.md) and [public workflow](examples/rpc_workflow.md).

### File version

Save as `lib/case_studies/rpc_client.ex` (create the directory first):

```elixir
defmodule CaseStudies.RpcHelpers do
  @compile :debug_info
  def await_reply(_server, reference, timeout) do
    receive do
      {:reply, ^reference, data} -> {:reply, data}
    after
      timeout -> :timeout
    end
  end
  def decode(data), do: data
end

defmodule CaseStudies.RpcClient do
  @compile :debug_info
  def request(server, reference, input, timeout) do
    message = {:request, reference, input}
    send(server, message)
    case CaseStudies.RpcHelpers.await_reply(server, reference, timeout) do
      {:reply, data} -> CaseStudies.RpcHelpers.decode(data)
      :timeout -> :timeout
    end
  end
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.RpcHelpers do
  @compile :debug_info
  def await_reply(_server, reference, timeout) do
    receive do
      {:reply, ^reference, data} -> {:reply, data}
    after
      timeout -> :timeout
    end
  end
  def decode(data), do: data
end

defmodule CaseStudies.RpcClient do
  @compile :debug_info
  def request(server, reference, input, timeout) do
    message = {:request, reference, input}
    send(server, message)
    case CaseStudies.RpcHelpers.await_reply(server, reference, timeout) do
      {:reply, data} -> CaseStudies.RpcHelpers.decode(data)
      :timeout -> :timeout
    end
  end
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
alias ReductionBounds.{Mailbox, RpcConditions, RpcCost, RpcProtocol, RpcServerContract, RpcTerm}
alias ReductionBounds.IntegerSize
cap = %RpcTerm.Size{nodes: 100, bytes: 32, integer_bits: 256}
{:ok, session} = RpcProtocol.new(7)
request = {:tuple3, {:atom, "request"}, {:ref, 7}, {:integer, 5}}
{:ok, conditions} = RpcConditions.new(session, request,
  request_size: cap, response_size: cap, message_size: cap,
  limits: Map.new(Mailbox.counters(), &{&1, 100}),
  protocol_limits: %{events: 100, client_sends: 1, server_sends: 1,
                     response_handlers: 1, retries: 0}, timeout: 0)
frame = %{message_size: cap, reply_size: cap, initial_messages: 10,
          arrivals: 10, inspections: 20, pattern_attempts: 20, guard_attempts: 20}
{:ok, server} = RpcServerContract.assume({CaseStudies.RpcHandler, :handle, 1},
  %IntegerSize{lower: 0, upper: 10, magnitude_bits: 4}, 30, frame)
rates = Map.new(RpcCost.operations() -- [:handle_request], fn op ->
  {op, %{cost_unit: if(RpcCost.owner(op) == :client, do: :client_work, else: :server_work),
         upper_bound: 2}}
end)
{:ok, cost_profile} = RpcCost.new(conditions, rates, server,
  initial_messages: 10, server_calls: 1)
{:ok, source} = ReductionBounds.infer_rpc_bound(
  {CaseStudies.RpcClient, :request, 4}, cost_profile, Keyword.merge(beam_options,
    calls: %{reply: {CaseStudies.RpcHelpers, :await_reply, 3},
             decode: {CaseStudies.RpcHelpers, :decode, 1}}))
source.source_correspondence
#=> :checked_under_contracts
source.client_source_bound
source.verification_scope
source.completion.theorem_status
#=> :not_established
```


### Read the source-node formula

`client_source_bound.formula` is `{:add, {:mul, 21, {:charge, :source_node}}, 1210}`:

```math
B_{\mathrm{RPC,source}}=21c_s+1210.
```

The coefficient 21 bounds local source-node work for this recognized client;
1210 is the separate client-model budget from the supplied profile. If the
local charge is declared to be one in compatible client-work units, this
expression evaluates to 1231. It still requires disjoint source/protocol
accounting and the explicit helper/mailbox association contracts. The server's
232-unit budget remains separate; a model completion rank does not prove this
source client terminates.


## Caller-supplied Lean proofs

This case defines its own zero-returning target. The API checks a supplied
value theorem for a Lynx-translated target; it does not infer a cost bound.

### File version

Save as `lib/case_studies/proof_zero.ex` (create the directory first):

```elixir
defmodule CaseStudies.ProofZero do
  @compile :debug_info
  def zero(), do: 0
end
```

```sh
mix compile
iex -S mix
```

In IEx:

```elixir
beam_options = []
```

### IEx version

Start `iex -S mix` and paste:

```elixir
compiled = Code.compile_string(~S"""
defmodule CaseStudies.ProofZero do
  @compile :debug_info
  def zero(), do: 0
end
""")
beam_options = [beam_binaries: Enum.map(compiled, &elem(&1, 1))]
```

### Analyze either version

```elixir
import Lynx.Lean
target = {CaseStudies.ProofZero, :zero, 0}
proof = ~LEAN"""
theorem zeroValue : Elixir.CaseStudies.ProofZero.«zero/0» = .ok (.integer 0) := by
  rfl
"""
{:ok, [{^target, {:ok, reports}}]} =
  ReductionBounds.verify([target], Keyword.put(beam_options, :postlude, proof))
Enum.map(reports, & &1.status)
```

**Lean file:** save the theorem (without `~LEAN` delimiters) as
`lean/case_studies_zero.lean`, then run in IEx with the same target-loading route:

```elixir
ReductionBounds.verify("case_studies_zero.lean", [target], beam_options)
```

The file is resolved relative to the current Mix project's `lean/` directory, not
as an Elixir source file. The [Lean verification guide](examples/verification.md)
explains recursion suffixes and translation-cycle diagnostics. A top-level
`{:ok, results}` can contain per-target errors; inspect every target result.

### Read the theorem rather than a cost expression

The checked declaration states a value equality:

```math
\operatorname{eval}(\texttt{CaseStudies.ProofZero.zero/0})
 =\operatorname{ok}(0).
```

It asserts normal return of zero in the translated value model. It supplies
no cost inequality `$C\leq B$`. To obtain a symbolic cost bound for the same
function, use the constant case's inference API. A `:ok` report records a
successful check of the supplied statement, not a stronger unstated property.


## Reproduce the maintained regression cases

From the repository root, after setup:

```sh
mix test --only case_study --trace
REDUCTION_BOUNDS_REPORT=1 mix test --only cost_contract_workflow --trace
REDUCTION_BOUNDS_REPORT=1 mix test --only port_workflow
mix test --only rpc_workflow
mix test test/reduction_bounds/struct_bound_test.exs test/reduction_bounds/periodic_bound_test.exs
```

These test selections exercise proof workflows and rejection cases. They do not
measure target runtime reductions. Choose a hardware profile using
[Test Performance Calibration](test_performance.md) before running controlled
full-suite performance comparisons. The [examples index](examples.md) links to
more detailed references for each family.
