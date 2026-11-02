import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Topology.Algebra.Module.FiniteDimension

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization`, actual Gram inverse normal projection formula. -/

namespace GlobalEmbedding.Paper

/-- The Gram operator of an injective finite-dimensional frame is symmetric, strictly
positive on every nonzero vector and invertible, including a zero source space.

Proof: adjoint identities show symmetry and identify its quadratic value with ‖Av‖².
Injectivity of A makes that value positive away from zero. The Gram kernel equals
ker A, so it is injective; finite source dimension gives bijectivity and an actual
continuous linear equivalence, witnessing invertibility.
Source: `prop:initialization`, positive Gram and normal projection formula. -/
theorem frame_gram_positive_invertible
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [CompleteSpace F] (A : E →L[ℝ] F) (hA : Function.Injective A) :
    (A.adjoint.comp A).IsSymmetric ∧
    (∀ v : E, v ≠ 0 → 0 < inner ℝ v ((A.adjoint.comp A) v)) ∧
    (A.adjoint.comp A).IsInvertible := by
  refine ⟨?_, ?_, ?_⟩
  · intro v w
    change inner ℝ (A.adjoint (A v)) w = inner ℝ v (A.adjoint (A w))
    rw [ContinuousLinearMap.adjoint_inner_left, ContinuousLinearMap.adjoint_inner_right]
  · intro v hv
    have hAv : A v ≠ 0 := by
      intro h
      apply hv
      apply hA
      simpa using h
    change 0 < inner ℝ v (A.adjoint (A v))
    rw [ContinuousLinearMap.adjoint_inner_right, real_inner_self_eq_norm_sq]
    exact sq_pos_of_pos (norm_pos_iff.mpr hAv)
  · have hG : Function.Injective (A.adjoint.comp A) :=
      A.adjoint_comp_self_injective_iff.mpr hA
    let e : E ≃L[ℝ] E :=
      (LinearEquiv.ofBijective (A.adjoint.comp A).toLinearMap
        ⟨hG, LinearMap.injective_iff_surjective.mp hG⟩).toContinuousLinearEquiv
    exact ⟨e, by ext v; rfl⟩

end GlobalEmbedding.Paper
