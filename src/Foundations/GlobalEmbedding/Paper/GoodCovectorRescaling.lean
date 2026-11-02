import GlobalEmbedding.Paper.GoodCovector

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Goodness depends only on the covector line, independently of any auxiliary
norm. Proof: nonzero scalar multiplication preserves nonzeroness and the literal
kernel, so the actual restricted true form is unchanged. Source: `defn:phase`,
normalization of good covectors for the best-phase maximum. -/
theorem good_covector_smul_iff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) (a : ℝ) (ha : a ≠ 0) :
    GoodCovector f hf x (a • ξ) ↔ GoodCovector f hf x ξ := by
  have hker : (a • ξ).ker = ξ.ker := by
    change LinearMap.ker (a • ξ.toLinearMap) = LinearMap.ker ξ.toLinearMap
    exact LinearMap.ker_smul ξ.toLinearMap a ha
  unfold GoodCovector
  rw [hker, smul_ne_zero_iff_right ha]

end GlobalEmbedding.Paper
