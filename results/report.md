# Isabelle/HOL bridge comparison

22 finite model/property pairs. Exhaustive reachability labeled 22 pairs.

The compiled Poly/ML executable ran on Linux 6.10.11-linuxkit aarch64 inside Docker.

The Isabelle2026 session build command took 13.55 s. Engine setup took 1.32 s.

The run used a 30 s wall limit per invocation. BridgeFuzz sampled up to 64 sequences of up to 16 steps per seed, with 30 seeds per pair. The metadata file records the finite work limits for the verifiers.

## Property support and detection

Support counts model/property pairs accepted by a method. A detection is a checked violation, or a SmartAxe alert on a pair labeled as a violation. For BridgeFuzz, a pair counts once if any seed finds it.

| Method | Supported pairs | Violating supported pairs found | Proved pairs | False static alerts |
| --- | ---: | ---: | ---: | ---: |
| pdr_cegar | 22/22 | 8/10 | 12 | 0 |
| pdr_concrete | 22/22 | 10/10 | 12 | 0 |
| smartaxe | 18/22 | 8/8 | 0 | 0 |
| bridgefuzz | 22/22 | 10/10 | 0 | 0 |
| scutum | 22/22 | 10/10 | 12 | 0 |
| bmc (4) | 22/22 | 2/10 | 0 | 0 |
| bmc (8) | 22/22 | 10/10 | 0 | 0 |
| bmc (16) | 22/22 | 10/10 | 0 | 0 |

## Per-run outcomes and resources

Wall time includes process launch. Compute time covers model construction, analysis, and any evidence checks in the exported HOL job. Peak RSS includes the Poly/ML runtime. Medians use supported runs that returned a result.

| Method | Runs | Outcomes | Wall ms | Compute ms | Peak RSS MiB |
| --- | ---: | --- | ---: | ---: | ---: |
| pdr_cegar | 22 | 2 inconclusive, 12 proved, 8 violation | 2.753 | 0.532 | 23.344 |
| pdr_concrete | 22 | 12 proved, 10 violation | 2.025 | 0.137 | 23.344 |
| smartaxe | 22 | 8 alert, 10 no_alert, 4 unsupported | 1.870 | 0.072 | 23.406 |
| bridgefuzz | 660 | 360 no_finding, 300 violation | 1.934 | 0.333 | 23.406 |
| scutum | 22 | 12 proved, 10 violation | 2.904 | 0.173 | 23.406 |
| bmc (4) | 22 | 20 no_finding, 2 violation | 1.822 | 0.092 | 23.406 |
| bmc (8) | 22 | 12 no_finding, 10 violation | 1.922 | 0.101 | 23.406 |
| bmc (16) | 22 | 12 no_finding, 10 violation | 1.879 | 0.100 | 23.406 |

## Results by model and property

For BridgeFuzz, hit counts use completed sampling runs as the denominator. The first-finding time is the median compute time of successful seeds for that case. PDR/CEGAR results include the number of refinement rounds.

| Case | Property | Reachability label | pdr_cegar | pdr_concrete | smartaxe | bridgefuzz | scutum | bmc (4) | bmc (8) | bmc (16) |
| --- | --- | --- | --- | --- | --- | --- | --- | --- | --- | --- |
| once-reference/1 | at-most-once credit | proved | proved (3 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| once-reference/2 | at-most-once credit | proved | proved (6 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| once-variation/1 | at-most-once credit | violation at depth 6 | violation (10 refinements) | violation | alert | 30/30 hits, 0.052 ms | violation | no_finding | violation | violation |
| once-variation/2 | at-most-once credit | violation at depth 6 | inconclusive (12 refinements) | violation | alert | 30/30 hits, 0.469 ms | violation | no_finding | violation | violation |
| backing-reference/1 | finalized backing | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| backing-reference/2 | finalized backing | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| backing-variation/1 | finalized backing | violation at depth 4 | violation (3 refinements) | violation | alert | 30/30 hits, 0.042 ms | violation | violation | violation | violation |
| backing-variation/2 | finalized backing | violation at depth 4 | violation (6 refinements) | violation | alert | 30/30 hits, 0.379 ms | violation | violation | violation | violation |
| exclusivity-reference/1 | refund and payout exclusivity | proved | proved (0 refinements) | proved | unsupported | 0/30 hits | proved | no_finding | no_finding | no_finding |
| exclusivity-reference/2 | refund and payout exclusivity | proved | proved (0 refinements) | proved | unsupported | 0/30 hits | proved | no_finding | no_finding | no_finding |
| exclusivity-variation/1 | refund and payout exclusivity | violation at depth 6 | violation (6 refinements) | violation | unsupported | 30/30 hits, 0.048 ms | violation | no_finding | violation | violation |
| exclusivity-variation/2 | refund and payout exclusivity | violation at depth 6 | inconclusive (10 refinements) | violation | unsupported | 30/30 hits, 0.412 ms | violation | no_finding | violation | violation |
| authorization-reference/1 | credit authorization | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| authorization-reference/2 | credit authorization | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| authorization-variation/1 | credit authorization | violation at depth 5 | violation (5 refinements) | violation | alert | 30/30 hits, 0.056 ms | violation | no_finding | violation | violation |
| authorization-variation/2 | credit authorization | violation at depth 5 | violation (10 refinements) | violation | alert | 30/30 hits, 0.455 ms | violation | no_finding | violation | violation |
| agreement-reference/1 | recipient and amount agreement | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| agreement-reference/2 | recipient and amount agreement | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| agreement-variation/1 | recipient and amount agreement | violation at depth 5 | violation (5 refinements) | violation | alert | 30/30 hits, 0.059 ms | violation | no_finding | violation | violation |
| agreement-variation/2 | recipient and amount agreement | violation at depth 5 | violation (10 refinements) | violation | alert | 30/30 hits, 0.466 ms | violation | no_finding | violation | violation |
| published-fragment/1 | at-most-once credit | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |
| published-fragment/2 | at-most-once credit | proved | proved (0 refinements) | proved | no_alert | 0/30 hits | proved | no_finding | no_finding | no_finding |

## PDR ablation

Both PDR configurations reached a definitive verdict in 20 pairs. PDR/CEGAR was faster by compute time in 1 of those pairs. It made 64 refinement rounds across the paired runs.

## Reading the raw results

The raw JSON Lines records include each budget, seed, model witness depth, work count, and timing. Evidence IDs denote states of the finite model for certificates and traces, and zero-based rule indices for static alerts.

Work counts states expanded for reachability and BMC, search steps for PDR, path and flow rows for SmartAxe, sampled steps for BridgeFuzz, and exploration rounds for Scutum. Refinement counts record abstraction refinements for PDR/CEGAR and blocked infeasible candidates for Scutum.
