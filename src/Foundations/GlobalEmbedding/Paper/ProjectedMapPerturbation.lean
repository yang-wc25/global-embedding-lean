import Mathlib.Analysis.InnerProductSpace.Projection.Basic

/-!
# Pointwise projected second-jet perturbation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and stability of the selector margin.
This compares both projected maps in their common ambient Euclidean codomain.
-/

namespace GlobalEmbedding.Paper

/-- Perturbing a map and its normal projection costs the map error plus the
projection error multiplied by the old map norm.

Proof: write P′Q′−PQ=P′(Q′−Q)+(P′−P)Q. Orthogonal projection has operator norm
at most one; use the triangle inequality and submultiplicativity of operator norm.
Source: `prop:initialization`, projected second-jet comparison. -/
theorem projected_map_perturbation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (K L : Submodule ℝ F) [K.HasOrthogonalProjection] [L.HasOrthogonalProjection]
    (Q Q' : E →L[ℝ] F) :
    ‖L.starProjection.comp Q' - K.starProjection.comp Q‖ ≤
      ‖Q' - Q‖ + ‖L.starProjection - K.starProjection‖ * ‖Q‖ := by
  have heq : L.starProjection.comp Q' - K.starProjection.comp Q =
      L.starProjection.comp (Q' - Q) +
        (L.starProjection - K.starProjection).comp Q := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, map_sub]
    abel
  rw [heq]
  calc
    _ ≤ ‖L.starProjection.comp (Q' - Q)‖ +
        ‖(L.starProjection - K.starProjection).comp Q‖ := norm_add_le _ _
    _ ≤ ‖L.starProjection‖ * ‖Q' - Q‖ +
        ‖L.starProjection - K.starProjection‖ * ‖Q‖ :=
      add_le_add (ContinuousLinearMap.opNorm_comp_le _ _)
        (ContinuousLinearMap.opNorm_comp_le _ _)
    _ ≤ _ := by
      have h := mul_le_mul_of_nonneg_right L.starProjection_norm_le (norm_nonneg (Q' - Q))
      nlinarith

end GlobalEmbedding.Paper
