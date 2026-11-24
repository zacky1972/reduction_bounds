# Issue 8: heavy regression isolation

Measured source: `887d7b7`, clean for all four commands. Remote branch `8` was
reviewed at `6b30d2df19c13dcac52a614fef1802a3f56e456a` together with the revised
Issue 8 plan. Linux x86-64, Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0, locked
dependencies unchanged. Parent commands used `ERL_FLAGS='+S 4:4'`,
`LEAN_NUM_THREADS=2`, named modules and caching. Each command prepared a fresh
isolated Mix build/cache and the runner before timing. Dependency Lean build
artifacts were reused. No other tests or checks ran concurrently with measurement.

## Isolation changes

The previous two synchronous regression modules are separated into five groups:

- Five independently scheduled proof-family comparisons, preserving the ordered
  named, repeated, bypassed and embedded requests within each family.
- Four independently scheduled cache scenarios, each with a fresh shared-source
  identity whose keys propagate through the complete dependent closure.
- Two asynchronous preparation/context integration cases using private keys or
  temporary compiled-dependency files.
- One synchronous public mode comparison, preserving environment restoration and
  private fixture cleanup.
- One synchronous independent-VM publication case, retaining two concurrent child
  publishers followed by a third warm reader.

All 13 cases and 49 verification invocations remain. Cache scenarios now explicitly
require a fully uncached first request, and a distinct second target must be
uncached before its own warm retry. These checks make cold/warm preconditions
independent of other tests. Fresh source identities are deliberately regenerated
in each VM, including warm-suite repetitions; this can add preparation work
compared with the earlier shared-identity regression. The test-level allowance
for asynchronous multi-request cases is five minutes. Existing preparation Task,
child Task, publication-test and public target deadlines remain unchanged.

Child VMs have explicit one-job budgets, one Lean thread and two BEAM schedulers.
Their budgets do not share parent capacity. Keeping publication synchronous avoids
other parent proof submissions during the child stage. The runner is built via
the supported Lynx Lake API before forking. Both Task results must be successful
commands with a nonempty accepted report set; failures cannot be skipped by a
pattern-filtering comprehension. At least one publisher must perform uncached
work, and the third VM must read entirely cached accepted artifacts.

No production proof, cache-key semantics, verification boundary, Lean options or
default budget changed. The default of 2 remains provisional. See the
[isolation guide](../regression_isolation.md) for state ownership and lifecycle.

## Controlled cohort comparison

Both samples use the same source, seed 0, parent jobs 2, threads 2, and an empty
verification cache. Only ExUnit max cases and the output path differ.

| ExUnit max cases | Command seconds | Sampled RSS, GiB | Sampled CPU, % | Peak per-VM admission | Verification calls | Passed |
| ---: | ---: | ---: | ---: | ---: | ---: | ---: |
| 1 | 203.080 | 2.425 | 106.4 | 1 | 49 | 13 |
| 4 | 120.047 | 2.430 | 189.9 | 2 | 49 | 13 |

The parallel cohort sample was **40.9% shorter**. This is one cold sample per
configuration, not a statistical guarantee or whole-suite/Mac speedup estimate.
All regression assertions are the same between these samples, including the
new cold-state guards. Both report 68 cached module reports.

`max_cases=1` serializes ExUnit cases; the publication case still intentionally
starts two child VMs concurrently in both configurations. Peak admission is
per VM, not a count of every active OS process. Child publication can therefore
have two concurrent runners while each reports a one-job peak. RSS includes the
command's sampled process tree, can count shared pages repeatedly, and can be
dominated by publication even in the serial case. CPU 100% represents one core.
Queue and request duration sums overlap and do not partition suite wall time.

Reproduce with `mix reduction_bounds.bench --suite-only --seed 0 --max-cases 4`,
`--test-files` selecting the five files listed in the isolation guide, and a new
`--output`. Set the parent environment above and
`REDUCTION_BOUNDS_LEAN_JOBS=2`. Repeat separately with `--max-cases 1` and a different
output path. Do not use trace or slowest-test mode to compare throughput.

## Additional validation

| Scope | Seed | ExUnit max cases | Parent jobs | Command seconds | Sampled RSS, GiB | Passed |
| --- | ---: | ---: | ---: | ---: | ---: | ---: |
| Regression cohort | 42 | 24 | 4 | 79.411 | 4.510 | 13 |
| Ordinary full suite | 42 | 4 | 2 | 628.623 | 2.512 | 336 |

The additional cohort run reached four parent jobs. Its seed, job limit and case
limit differ from the controlled pair; it is a correctness validation rather
than a controlled job-limit comparison or a reason to select a default.

All 336 full-suite tests passed (18 documentation tests and 318 other tests).
ExUnit reported 627.755 seconds: 544.888 async and 82.868 sync. The full run
observed 299 verification invocations. Source/callee replay, invalidation,
negative/unfinished proofs, API errors, queueing, cancellation and supervisor
restart checks remain enabled. This is one full-suite seed/case setting; a cold
full suite with parent jobs 2/max_cases 24 was not validated here. Earlier
calibration had deadline failures at that setting. No deadline was extended to
hide overload.

Do not attribute an earlier/full-suite timing difference solely to scheduling:
the new private cache identities deliberately strengthen cold-state coverage and
can require additional preparation. The controlled cohort pair isolates the
case-scheduling comparison within the final implementation more closely.

All four event streams confirm five distinct family identities with four ordered
requests each, and four distinct cache identities with 6/5/5/4 requests. Initial
cache requests are accepted and uncached. Warm, shared-only, bypass, source/option
invalidation, invalid targets, invalid shared modules and skipped dependents have
the expected cache/status patterns. Repeated family requests are cached and both
bypass modes are uncached. Each run includes three distinct child VM identifiers,
all with one-job limits; all returned nonempty accepted reports and the final
reader was fully cached. Negative request reports are not suite failures.

`mix check` and `mix docs --warnings-as-errors` passed before measurement. Final
formatting, spelling and documentation checks cover this report. No full test
matrix or default selection is claimed.

## Evidence

- [Serial cohort](issue8-heavy-serial.json)
- [Parallel cohort](issue8-heavy-parallel.json)
- [Additional seed/concurrency](issue8-heavy-seed42.json)
- [Full suite](issue8-heavy-full.json)

Each JSON has an adjacent matching `_artifacts` directory with preparation logs,
suite logs and per-request JSONL events. Absolute paths identify the original
workspace; use adjacent artifacts after relocating the checkout.

[Static checks](issue8-heavy-validation_artifacts/check.log),
[initial documentation build](issue8-heavy-validation_artifacts/docs.log),
[event validation](issue8-heavy-validation_artifacts/events.log).
