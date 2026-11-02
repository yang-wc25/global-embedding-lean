import GlobalEmbedding.External.CalabiYau.Mathlib.Analysis.Holder.Basic
import GlobalEmbedding.Paper.PeriodicCAlphaNormFromEuclideanHolder

/-!
# Apply the external Euclidean Hölder gauge to the original periodic norm

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382; gauge API from wxkj99/calabi-yau at
91b1ddf000c7028bc42ae6102eba0e2042eb37ff, CalabiYau/Mathlib/Analysis/Holder/Basic.lean.
DAG node: `balanced-inverse-norm-from-calabi-gauge`.
-/

open Set
open scoped NNReal

namespace GlobalEmbedding.Paper

/-- A finite bound on the actual external Euclidean Hölder gauge bounds the original
periodic flat-torus Hölder norm, without identifying these two definitions.

Proof: the source gauge controls every actual spatial jet and the top jet's Hölder
constant on the univ subtype. Evaluate that estimate on the canonical subtype lifts to
obtain the Euclidean HolderWith estimate. The proved lattice-minimum comparison then
bounds the original periodic norm by (k+2)C, also in dimension zero.
Source: `lem:balanced`, periodic Schauder interface; CalabiYau Holder.Basic APIs. -/
theorem periodicCAlphaNorm_le_of_calabi_gauge
    {a N k : ℕ} {α C : ℝ≥0} (f : PeriodicCAlphaFunction a N k (α : ℝ))
    (h : CalabiYau.Schauder.eContDiffHolderGaugeOn k α univ f.toFun ≤ C) :
    ‖f‖ ≤ (k + 2 : ℕ) * (C : ℝ) := by
  apply periodicCAlphaNorm_le_of_euclidean_holder f
  · intro j hj x
    exact CalabiYau.Schauder.spatialJet_norm_le h hj (mem_univ x)
  · have ht := CalabiYau.Schauder.topSpatialJet_holderWith_restrict h
    intro x y
    exact ht ⟨x, mem_univ x⟩ ⟨y, mem_univ y⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.periodicCAlphaNorm_le_of_calabi_gauge
