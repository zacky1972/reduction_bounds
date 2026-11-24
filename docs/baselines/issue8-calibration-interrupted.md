# Issue 8: interrupted job-budget calibration

Measured source: `79d7d6b` (clean committed checkout). Linux x86-64,
Elixir 1.20.5, OTP 29.1.2, Lean 4.35.0. All planned runs used seed 0,
ExUnit max_cases 24, Lean threads 2, named modules and caching enabled.
No public target or deliberate-test deadlines were increased.

The experiment was interrupted by the user before the matrix completed.
Raw checkpoint statuses remain unchanged; `running` in these saved files
indicates an interrupted configuration, not a currently active process.

| Jobs | Cache | Command seconds | Result |
| ---: | --- | ---: | --- |
| 2 | cold | 710.039 | 328 tests, 2 failures |
| 2 | warm | 563.826 | 328 passed |
| 4 | cold | incomplete | Interrupted after 274 completed tests, no failures observed |
| 4 | warm | not run | Not measured |
| 1 | cold/warm | not run | Not measured |

Both jobs=2 cold failures were public API timeouts in PortSourceProofTest
and PortWorkflowTest. They are real test failures, distinct from the
intentional negative-proof/timeout events in a passing suite.

There is no completed comparison of job budgets and no basis to select a
new default. The default remains a provisional 2. Do not compare an
interrupted/failed run as though it were a successful throughput result.
Linux observations do not establish the best setting on the target Mac.

The implementation adds `mix reduction_bounds.calibrate` to execute the
configurations sequentially with isolated cold/warm caches, explicit child
environments, rotating order for repeated trials, metadata/phase/count
validation and JSON/Markdown summaries. See `docs/job_calibration.md`.

Validation: 12 focused benchmark/calibration tests passed; strict Credo
passed on the measured source. The full `mix check` and documentation build
passed before the environment-checkpoint serialization fix; they were not
repeated after that fix. The fix has a JSON serialization regression and
was exercised by the completed jobs=2 runs and partial jobs=4 run.

Raw checkpoints, suite logs and events are preserved in the adjacent
`issue8-calibration-interrupted_artifacts` directory. Absolute paths in
reports refer to the original workspace. Use the adjacent copies after
relocating the checkout. No benchmark is left running.
