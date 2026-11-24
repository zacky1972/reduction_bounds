<!-- cspell:words uncacheable -->
# Conditional runner optimization review

Evidence: complete. Benchmark status: "completed".
deferred: review controlled throughput, attribution, supported APIs and lifecycle checks before implementing either optimization

## runner_empty / cold

Events: available. Command wall: 680 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| empty_probe | 1 | 1 | 179.577 | 179.577 |

## runner_empty / warm_1

Events: available. Command wall: 774 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| empty_probe | 1 | 1 | 182.881 | 182.881 |

## runner_empty / warm_2

Events: available. Command wall: 704 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| empty_probe | 1 | 1 | 172.994 | 172.994 |

## runner_empty / warm_3

Events: available. Command wall: 741 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| empty_probe | 1 | 1 | 166.631 | 166.631 |

## runner_runtime / cold

Events: available. Command wall: 2248 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| uncacheable_or_bypassed | 1 | 1 | 1389.036 | 1384.036 |

## runner_runtime / warm_1

Events: available. Command wall: 1503 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| uncacheable_or_bypassed | 1 | 1 | 683.466 | 678.466 |

## runner_runtime / warm_2

Events: available. Command wall: 1518 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| uncacheable_or_bypassed | 1 | 1 | 775.691 | 769.691 |

## runner_runtime / warm_3

Events: available. Command wall: 1401 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| uncacheable_or_bypassed | 1 | 1 | 660.148 | 654.148 |

## integer_cost / cold

Events: available. Command wall: 9854 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| shared_cacheable_miss | 1 | 1 | 8967.027 | 664.027 |

## integer_cost / warm_1

Events: available. Command wall: 2732 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 1 | 1 | 1896.558 | 655.558 |

## integer_cost / warm_2

Events: available. Command wall: 2780 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 1 | 1 | 1953.406 | 639.406 |

## integer_cost / warm_3

Events: available. Command wall: 2819 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 1 | 1 | 1938.088 | 723.088 |

## port_source / cold

Events: available. Command wall: 13428 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| shared_cacheable_miss | 1 | 1 | 12436.907 | 640.9069999999992 |

## port_source / warm_1

Events: available. Command wall: 2759 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 1 | 1 | 1877.104 | 709.104 |

## port_source / warm_2

Events: available. Command wall: 3126 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 1 | 1 | 2085.833 | 689.8330000000001 |

## port_source / warm_3

Events: available. Command wall: 2858 ms. Exit: 0.

| Request group | Requests | Valid timing pairs | Known call ms, sum | Paired residual ms, sum |
| --- | ---: | ---: | ---: | ---: |
| fully_cached | 1 | 1 | 2000.066 | 765.066 |

Residuals exclude preparation/admission waits and are not isolated startup measurements. Sums overlap and are not suite-time partitions. Missing policy is unknown; an uncached report alone does not prove a cacheable cold miss. A complete event review does not mean a passing benchmark or justify either backend change.
