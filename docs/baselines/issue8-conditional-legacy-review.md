# Conditional runner optimization review

Evidence: complete. Benchmark status: "completed".
deferred: review controlled throughput, attribution, supported APIs and lifecycle checks before implementing either optimization

## suite / cold

Events: available. Command wall: 628623 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 36 | 36 | 79818.835 | 30214.834999999995 |
| policy_unknown | 195 | 195 | 775559.1589999999 | 163432.15900000007 |
| unsuccessful | 66 | 66 | 229516.28599999993 | 57233.28600000001 |

Residuals exclude preparation/admission waits and are not isolated startup measurements. Sums overlap and are not suite-time partitions. Missing policy is unknown; an uncached report alone does not prove a cacheable cold miss. A complete event review does not mean a passing benchmark or justify either backend change.
