import GlobalEmbedding.Paper.NormalProjectionGramFormula

namespace GlobalEmbedding.Paper

/-- The actual Gram coefficient operator is a left inverse to an injective frame,
and its reverse composition is the actual range projection.

Proof: the first equality is the inverse Gram identity. For the second, the proved
normal Gram formula and complement identity give equality after subtracting both
sides from the identity; cancel that subtraction.
Source: local-frame expansion of `defn:phase` and `prop:initialization`. -/
theorem frame_gram_inverse_identities
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A : E →L[ℝ] F) (hA : Function.Injective A) :
    ((A.adjoint.comp A).inverse.comp A.adjoint).comp A =
      ContinuousLinearMap.id ℝ E ∧
    A.comp ((A.adjoint.comp A).inverse.comp A.adjoint) =
      (LinearMap.range A.toLinearMap).starProjection := by
  have hG := frame_gram_positive_invertible A hA
  constructor
  · ext v
    exact hG.2.2.inverse_apply_self v
  · have h := (normal_projection_gram_formula A hA).2.2.2
    rw [Submodule.starProjection_orthogonal] at h
    exact (sub_right_inj.mp h).symm

end GlobalEmbedding.Paper
