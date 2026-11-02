import GlobalEmbedding.Paper.PeriodicCAlphaNormedGroup

/-!
# The actual real normed space of periodic Hölder functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-ambient-space`.
-/

namespace GlobalEmbedding.Paper

/-- The real normed-space structure on the actual periodic Hölder carrier.

The scalar operation is the actual pointwise one, its norm is the real Hölder formula, and
its distance/topology are those of the already constructed normed additive group. This uses
the fully proved norm core; no completeness property is assumed or asserted here.
Source: `lem:balanced`, usual periodic Hölder ambient-space expansion. -/
noncomputable instance periodicCAlphaNormedSpace {a N k : ℕ} {α : ℝ} :
    NormedSpace ℝ (PeriodicCAlphaFunction a N k α) :=
  NormedSpace.ofCore periodicCAlphaNormedCore

#print axioms periodicCAlphaNormedSpace

end GlobalEmbedding.Paper
