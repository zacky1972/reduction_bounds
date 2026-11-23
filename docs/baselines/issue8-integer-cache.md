# Issue 8: integer shared-module pilot

Measured source: `aac7f03f8dd3ada3cccb566cc4cb05d8a389cdbd` (clean working tree for all three variants).
Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0, Linux x86-64; locked dependencies
are unchanged. Raw reports contain exact versions, environment settings,
source status, timings, memory samples, and per-module cache flags.

## Reproduction

Run each configuration separately, with the same machine settings:

```sh
ERL_FLAGS='+S 4:4' LEAN_NUM_THREADS=4 \
  REDUCTION_BOUNDS_PROOF_MODE=embedded REDUCTION_BOUNDS_PROOF_CACHE=off \
  mix reduction_bounds.bench --no-suite \
  --workloads integer_analysis,integer_cost,bound_transfer --repetitions 3 \
  --max-cases 4 --output _build/issue8-integer-embedded.json
```

Repeat with `REDUCTION_BOUNDS_PROOF_MODE=named` and
`REDUCTION_BOUNDS_PROOF_CACHE=shared` for shared theories only, then with
`REDUCTION_BOUNDS_PROOF_CACHE=on` for shared theories and target artifacts.
Use separate output paths. Each variant prepares an isolated Mix build; each
workload starts with an empty verification cache, followed by three warm attempts
in fresh VMs. Dependency Lean build artifacts already existed. Measurements ran
after the full-suite validation, without a concurrent test or analysis command.

## Command wall time

Cold verification-cache samples, seconds:

| Workload | Embedded | Shared only | Shared and targets |
| --- | ---: | ---: | ---: |
| `integer_analysis` | 4.177 | 6.039 | 6.239 |
| `integer_cost` | 5.772 | 9.179 | 9.442 |
| `bound_transfer` | 12.011 | 12.623 | 13.705 |

Warm attempts, median of three samples, seconds:

| Workload | Embedded | Shared only | Shared and targets |
| --- | ---: | ---: | ---: |
| `integer_analysis` | 3.826 | 2.724 | 2.255 |
| `integer_cost` | 5.640 | 3.523 | 3.285 |
| `bound_transfer` | 12.124 | 7.018 | 4.780 |

The shared-only configuration still checks every target proof. It isolates the
benefit of reusing common theories from the additional benefit of reusing an
identical target. Separate regression tests verify theory reuse across different
targets and unchanged public claims, assumptions, and audited theorem names.
Cold splitting adds module/import overhead; warm results must not be presented
as first-call latency. These samples are observations, not a statistically
established performance guarantee or a whole-suite speedup estimate.

## Sampled process-tree memory

Maximum across the cold and three warm runs, GiB:

| Workload | Embedded | Shared only | Shared and targets |
| --- | ---: | ---: | ---: |
| `integer_analysis` | 1.14 | 1.19 | 1.19 |
| `integer_cost` | 1.22 | 1.22 | 1.22 |
| `bound_transfer` | 1.50 | 1.30 | 1.38 |

RSS is sampled every 100 ms and summed over the process tree; shared pages may be
counted more than once. It is not an exact OS high-water mark.

## Validation

- Ordinary full suite: **291 passed** (18 documentation tests, 273 other tests); `Finished in 864.9 seconds (12.2s async, 852.7s sync)`.
- Final focused cache/registry tests: 11 passed, including source/options changes,
  invalid proofs, `sorry`, failed shared dependencies, bypass modes, and API parity.
- `mix check` and `mix docs --warnings-as-errors` passed.

The full-suite validation used existing verification artifacts. It verifies
correctness and is not a controlled throughput comparison against the stage 1
run. Other proof families remain uncached; no test-concurrency defaults or
persistent runner pool were introduced by this pilot.

[Full-suite output](issue8-integer-validation_artifacts/full-suite.log),
[focused tests](issue8-integer-validation_artifacts/focused.log),
[static checks](issue8-integer-validation_artifacts/check.log), and
[documentation build](issue8-integer-validation_artifacts/docs.log) retain the
validation results.

Raw benchmark reports:

- [Embedded source](issue8-integer-embedded.json)
- [Shared theories only](issue8-integer-shared.json)
- [Shared theories and targets](issue8-integer-named.json)

Each report has a corresponding `_artifacts` directory containing preparation
logs, command output, and verification events. Absolute paths describe the
original run; use the matching files beside these reports after moving the
checkout. See [benchmarking](../benchmarking.md) for interpretation and bypass
commands.
