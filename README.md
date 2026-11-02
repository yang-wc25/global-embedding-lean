# Global embedding in Lean

This library proves the closed parallelizable small-image isometric embedding theorem.
For a closed smooth parallelizable manifold of dimension n ≥ 3, every smooth
positive definite metric and every radius r > 0 admit a smooth phase-regular
isometric embedding into the radius-r ball in Euclidean dimension n(n+1)/2+1.
Empty and disconnected sources are included.

## Entry points

Import `GlobalEmbedding` for the complete library. The main declarations are:

- `GlobalEmbedding.Main.endpoint_main`
- `GlobalEmbedding.Main.original_sameMetric_phase_embedding`
- `GlobalEmbedding.Main.original_paired_probes`
- `GlobalEmbedding.Continuation.RepairClosure.original_small_exact_immersion_candidate`

`endpoint_main` proves `GlobalEmbedding.Main.EndpointMainTarget`: the same map
is smooth, has the prescribed induced metric, has injective differential,
is phase regular, is a topological embedding, and has image in the requested ball.
The upgrade retains the original C² approximation norm. The paired probes
include arbitrary smooth chart-supported cutoffs and all parameter estimates.

## Source organization

| Directory | Mathematics |
| --- | --- |
| `src/Foundations` | Differential geometry, selectors, analytic foundations and theorem entry modules |
| `src/Analysis` | Smoothing and auxiliary norm comparisons |
| `src/Geometry` | Buffered charts, collars and finite covering constructions |
| `src/Initialization` | Colored approximation and frequency-independent reference data |
| `src/Increments` | Finite positive increments and their quantitative estimates |
| `src/Repair` | The actual metric-correction constructions used by the proofs |
| `src/Probes` | Same-metric parameter families and paired responses |
| `src/Upgrade` | Incidence, avoidance, protection and the embedding upgrade |
| `src/Main` | General probes and the final embedding theorem |

The mathematical modules retain their original names; Lake maps each group to
its source directory. For example, `Main.OriginalUpgradeMain` is in
`src/Main/Main/OriginalUpgradeMain.lean`.

## Build

Lean 4.35.0 and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679` are pinned in the project files.

```sh
lake update
lake exe cache get
lake build
```

The source theorem is the closed parallelizable branch of
*Small-image isometric embeddings with parallelizable and stably trivial tangent bundles*.
The Lean modules retain their mathematical source references and attribution.

Third-party mathematical source licenses and notices are in [THIRD_PARTY](THIRD_PARTY/README.md).
