import GlobalEmbedding.Paper.FrameGramInvertible

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization`, actual Gram inverse normal projection formula. -/

namespace GlobalEmbedding.Paper

/-- The normal projection of an injective frame is I−A(A†A)⁻¹A†, and the same Gram
operator is symmetric, strictly positive and invertible.

Proof: A(A†A)⁻¹A†z lies in range A. Its difference from z lies in the orthogonal
complement because applying A† gives zero by the proved Gram inverse identity.
The characterization of orthogonal projection identifies this expression with the
tangent projection. The normal projection is identity minus that projection.
Source: `prop:initialization`, full normal-projection Gram formula, including n=0. -/
theorem normal_projection_gram_formula
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A : E →L[ℝ] F) (hA : Function.Injective A) :
    (A.adjoint.comp A).IsSymmetric ∧
    (∀ v : E, v ≠ 0 → 0 < inner ℝ v ((A.adjoint.comp A) v)) ∧
    (A.adjoint.comp A).IsInvertible ∧
    (LinearMap.range A.toLinearMap)ᗮ.starProjection =
      ContinuousLinearMap.id ℝ F -
        A.comp ((A.adjoint.comp A).inverse.comp A.adjoint) := by
  have hG := frame_gram_positive_invertible A hA
  refine ⟨hG.1, hG.2.1, hG.2.2, ?_⟩
  have hT : (LinearMap.range A.toLinearMap).starProjection =
      A.comp ((A.adjoint.comp A).inverse.comp A.adjoint) := by
    ext z
    apply Submodule.eq_starProjection_of_mem_orthogonal
    · exact ⟨(A.adjoint.comp A).inverse (A.adjoint z), rfl⟩
    · rw [ContinuousLinearMap.orthogonal_range]
      change A.adjoint (z - A ((A.adjoint.comp A).inverse (A.adjoint z))) = 0
      rw [map_sub]
      change A.adjoint z - (A.adjoint.comp A)
        ((A.adjoint.comp A).inverse (A.adjoint z)) = 0
      rw [hG.2.2.self_apply_inverse, sub_self]
  rw [Submodule.starProjection_orthogonal, hT]

end GlobalEmbedding.Paper
