# Small-image isometric embeddings in Lean

**The main theorem is proved in Lean. Start with [MainTheorem.lean](MainTheorem.lean).**

Let $M$ be a closed smooth parallelizable manifold of dimension $n\geq3$,
and let $g$ be a smooth positive definite Riemannian metric on $M$.
For every $r>0$, there is a smooth phase-regular embedding

$$
F:M\longrightarrow\mathbb R^{n(n+1)/2+1},\qquad
F^*\langle\cdot,\cdot\rangle=g,\qquad F(M)\subset B_r(0).
$$

Empty and disconnected sources are included. This is the closed parallelizable
branch of *Small-image isometric embeddings with parallelizable and stably
trivial tangent bundles*.

## Where to read

| Question | File |
| --- | --- |
| What exactly is the theorem, including every input and output? | [MainTheorem.lean](MainTheorem.lean) — `GlobalEmbedding.small_image_isometric_embedding` |
| How does the proof work? | [Proof guide](docs/PROOF_GUIDE.md) |
| Where is the final proof assembled? | [OriginalUpgradeMain.lean](src/Main/OriginalUpgradeMain.lean) — `GlobalEmbedding.Main.endpoint_main` |
| Where is the independent statement definition? | [EndpointStatements.lean](src/Main/EndpointStatements.lean) — `EndpointMainTarget` |
| Where is the last geometric step? | [SmallImmersionUpgrade.lean](src/Main/SmallImmersionUpgrade.lean) |
| Where are the general paired probes constructed? | [GeneralOriginalProbes.lean](src/Main/GeneralOriginalProbes.lean) |

`MainTheorem.lean` displays the full statement and supplies its Lean-checked
proof. The same map is smooth, induces the prescribed metric, has injective
differential, is phase regular, is a topological embedding, and satisfies
the requested image bound. Smooth embedding is expressed by `ContMDiff`,
injectivity of `mfderiv`, and `IsEmbedding`.

## Check the proof

The project pins **Lean 4.35.0** and Mathlib commit
`56a005855ea17e0b0958f73ec801ae140b0a1679`.

```sh
lake exe cache get
lake build
lake env lean MainTheorem.lean
```

The last command checks the explicit main theorem and prints its axiom
dependencies: `propext`, `Classical.choice`, and `Quot.sound`, the standard
foundations used here. The underlying main endpoint also passed a complete
declaration audit and the official independent Comparator with its default
kernel on 2026-11-02. The detailed record is
[archived separately](https://github.com/yang-wc25/global-embedding/blob/e81c8183cb1d6c7ccd6ef7643fa292ec31afe991/coord/reviews/thm-main-acceptance.json).

To use the main result:

```lean
import MainTheorem
#check GlobalEmbedding.small_image_isometric_embedding
```

Import `GlobalEmbedding` to load all the component theorem entry modules.

## File organization

```text
MainTheorem.lean          Full main statement and proved public entry
README.md                Mathematical result and how to check it
docs/PROOF_GUIDE.md       Proof outline and source reading order
src/
  Main/                  Final assembly and general probe construction
  Initialization/        Small-image starting maps and reference data
  Increments/            Finite metric increments and quantitative estimates
  Repair/                Actual metric-correction constructions
  Probes/                Same-metric families and paired responses
  Upgrade/               Incidence, avoidance and embedding upgrade
  Geometry/              Buffered charts, collars and coverings
  Analysis/              Smoothing and norm comparisons
  Foundations/           Source definitions, selectors and component theorems
THIRD_PARTY/             Upstream licenses and attribution
```

The implementation modules retain their mathematical names. Lake maps the
topic directories to those modules; the proof guide gives direct links to
the relevant files. Third-party mathematical source licenses and notices are
in [THIRD_PARTY](THIRD_PARTY/README.md).
