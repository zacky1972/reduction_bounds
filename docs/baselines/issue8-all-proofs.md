# Issue 8: shared modules across proof families

Measured source: `7bb23dbf6c7ade41f1a529b1a13a85a632048ba6`, with a clean working tree for all three configurations.
Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0, Linux x86-64. Locked dependencies are unchanged.
The registry now covers 25 shared theories and models. These six representative
workflows exercise composition, buffer sequences, Core execution, periodic rules,
Port source connection, and cost-contract comparison. The integer pilot has
[separate measurements](issue8-integer-cache.md).

## Reproduction

```sh
ERL_FLAGS='+S 4:4' LEAN_NUM_THREADS=4 \
  REDUCTION_BOUNDS_PROOF_MODE=embedded REDUCTION_BOUNDS_PROOF_CACHE=off \
  mix reduction_bounds.bench --no-suite \
  --workloads composed,circular_buffer_sequence,execution,periodic,port_source,contract_comparison \
  --repetitions 3 --max-cases 4 --output _build/issue8-all-proofs-embedded.json
```

Repeat separately with mode `named` and cache `shared`, then mode `named` and
cache `on`, using separate output paths. All three measurements used the same
source and machine settings. Each configuration prepares an isolated Mix build;
each workload clears only that isolated verification cache, runs once cold,
then runs three warm attempts in fresh VMs. Dependency Lean build artifacts
already existed. No tests or static checks ran concurrently with measurements.

## Command wall time

Cold verification-cache samples, seconds:

| Workload | Embedded | Shared only | Shared and targets |
| --- | ---: | ---: | ---: |
| `composed` | 2.917 | 5.832 | 5.949 |
| `circular_buffer_sequence` | 3.005 | 8.456 | 8.559 |
| `execution` | 3.742 | 7.078 | 7.288 |
| `periodic` | 1.611 | 2.874 | 2.724 |
| `port_source` | 9.208 | 13.430 | 13.121 |
| `contract_comparison` | 5.256 | 9.521 | 10.636 |

Warm attempts, median of three samples, seconds:

| Workload | Embedded | Shared only | Shared and targets |
| --- | ---: | ---: | ---: |
| `composed` | 2.508 | 3.851 | 3.186 |
| `circular_buffer_sequence` | 3.012 | 4.150 | 3.464 |
| `execution` | 3.616 | 3.589 | 3.100 |
| `periodic` | 1.717 | 2.309 | 1.869 |
| `port_source` | 9.525 | 6.755 | 3.153 |
| `contract_comparison` | 5.243 | 3.723 | 3.349 |

Shared-only runs recheck the target on every attempt. In the default configuration,
all reported modules were cache hits on each warm attempt. Embedded runs had no
cache hits. All 72 workload commands completed successfully, with every reported
module accepted and no incomplete verification requests.

These results do not show a universal speedup. Reusing the Port source and
contract theories helps; execution improves with target reuse. Small composition,
buffer-sequence and periodic cases are slower even when their artifacts are warm.
Splitting introduces per-module publication, import and artifact-loading costs;
all six cold cases are slower. This stage broadens safe reuse and coalesces
concurrent cold work. It does not remove runner startup or guarantee faster
whole-suite throughput. Three warm samples are observations, not a statistical
performance guarantee.

## Sampled process-tree memory

Maximum across each cold and three warm runs, GiB:

| Workload | Embedded | Shared only | Shared and targets |
| --- | ---: | ---: | ---: |
| `composed` | 1.13 | 1.13 | 1.13 |
| `circular_buffer_sequence` | 1.16 | 1.13 | 1.13 |
| `execution` | 1.17 | 1.17 | 1.17 |
| `periodic` | 1.02 | 1.11 | 1.12 |
| `port_source` | 1.35 | 1.26 | 1.27 |
| `contract_comparison` | 1.20 | 1.20 | 1.20 |

RSS is sampled every 100 ms and summed over the process tree; shared pages may
be counted more than once. This is not an exact OS high-water mark.

## Preparation and validation

Independent targets sharing a cold dependency closure are tested concurrently:
only one request compiles that closure and the other reuses its checked artifacts.
Independent closures can proceed concurrently. Tests also cover failed preparation,
owner termination, cancelled waiters, readiness invalidation and independent-VM
atomic artifact publication. Every family is checked through named, repeated,
cache-disabled and embedded paths, including all shared module reports and axiom
audits. Existing public API and source-replay tests remain enabled.

The full suite returned **303/304 passed** (18/18 documentation tests,
285/286 other tests), in 837.7 seconds. The sole failure was the new
independent-VM test parsing terminal diagnostics as JSON before its proof reports.
A test-only change tags the JSON record and reads it independently of diagnostics.
`mix test --failed --seed 0` then passed the remaining test (1 passed, 10.0 seconds).
The complete suite was not rerun after this parser-only change. Its existing
cache state and validation scheduling do not constitute a controlled whole-suite
throughput comparison with earlier stages.

`mix check` and `mix docs --warnings-as-errors` passed. Validation output:

- [Full suite before the test parser fix](issue8-all-proofs-validation_artifacts/full-suite-before-parser-fix.log)
- [Retry after the parser fix](issue8-all-proofs-validation_artifacts/parser-fix-retry.log)
- [Static checks](issue8-all-proofs-validation_artifacts/check.log)
- [Documentation build](issue8-all-proofs-validation_artifacts/docs.log)

Preparation readiness is local to one VM and advisory. Each fresh benchmark VM
can report itself as preparation owner while still obtaining all artifacts from
disk cache. Inspect per-module `cached` flags to distinguish compilation from
reuse. Coordination timings include dependency identity lookup and lease waiting;
they are included in runner wall time. Requests still submit their complete
ordered closure to the pinned sequential runner.

Raw reports and matching artifact directories:

- [Embedded source](issue8-all-proofs-embedded.json)
- [Shared theories only](issue8-all-proofs-shared.json)
- [Shared theories and targets](issue8-all-proofs-named.json)

Absolute paths in raw reports identify the original run. After moving the checkout,
use the matching files in the adjacent `_artifacts` directories. See
[shared proof modules](../shared_proofs.md) and [benchmarking](../benchmarking.md)
for architecture, controls and timing interpretation.
