import GlobalEmbedding.Paper.BoundedContinuousBilinearLift

/-!
# Exact values and uniform operator bound of actual bounded-family bilinear lifting

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 403–425.
DAG node: `bounded-continuous-bilinear-lift-spec`.
-/

open scoped BoundedContinuousFunction

namespace GlobalEmbedding.Paper

/-- Actual bounded-family lifting has its original pointwise values and no norm loss.

The value formula is the actual constructor data. The genuine uniform norm is bounded by
every original pointwise bilinear bound, so the actual bounded bilinear operator norm is
at most norm(B). This includes an empty parameter space. Source: uniform auxiliary-parameter
contraction in the proof of `lem:balanced`. -/
theorem boundedContinuousBilinearLift_spec
    {P X Y Z : Type*} [TopologicalSpace P]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    [NormedAddCommGroup Z] [NormedSpace ℝ Z]
    (B : X →L[ℝ] Y →L[ℝ] Z) :
    (∀ (f : P →ᵇ X) (g : P →ᵇ Y) p, boundedContinuousBilinearLift B f g p = B (f p) (g p)) ∧
      ‖boundedContinuousBilinearLift (P := P) B‖ ≤ ‖B‖ := by
  have hvalue (f : P →ᵇ X) (g : P →ᵇ Y) (p : P) :
      boundedContinuousBilinearLift B f g p = B (f p) (g p) := rfl
  refine ⟨hvalue, ContinuousLinearMap.opNorm_le_bound₂ _ (norm_nonneg B) ?_⟩
  intro f g
  apply (BoundedContinuousFunction.norm_le (by positivity)).mpr
  intro p
  rw [hvalue]
  exact B.le_of_opNorm₂_le_of_le le_rfl (f.norm_coe_le_norm p) (g.norm_coe_le_norm p)

#print axioms boundedContinuousBilinearLift_spec

end GlobalEmbedding.Paper
