<!-- cspell:words uncacheable -->
# Conditional runner optimization review

Evidence: complete. Benchmark status: "completed".
deferred: review controlled throughput, attribution, supported APIs and lifecycle checks before implementing either optimization

## suite / cold

Events: available. Command wall: 121557 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 9 | 9 | 18605.757999999998 | 7042.758 |
| shared_cacheable_miss | 14 | 14 | 92971.436 | 12456.436000000002 |
| target_or_other_miss | 4 | 4 | 8324.497 | 2998.497 |
| uncacheable_or_bypassed | 15 | 15 | 83219.106 | 12732.106 |
| unsuccessful | 7 | 7 | 16796.254999999997 | 6025.255000000001 |

Residuals exclude preparation/admission waits and are not isolated startup measurements. Sums overlap and are not suite-time partitions. Missing policy is unknown; an uncached report alone does not prove a cacheable cold miss. A complete event review does not mean a passing benchmark or justify either backend change.
