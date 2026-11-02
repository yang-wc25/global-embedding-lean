import GlobalEmbedding.Paper.SmoothFrameGramCoefficients

/-!
# The actual smooth Gram pairing right inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines477–489.
The actual frame inverse and its regularity are constructed, rather than assumed.
-/

noncomputable section
open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {V E : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]

/-- The literal Gram reconstruction B(B*B)^(-1), defined from the actual frame. -/
def freeGramRightInverse (B : V →L[ℝ] E) : V →L[ℝ] E :=
  B.comp (B.adjoint.comp B).inverse

/-- Injectivity of the actual frame makes the reconstruction a full-data pairing right inverse. -/
theorem freeGramRightInverse_spec (B : V →L[ℝ] E) (hB : Function.Injective B) :
    B.adjoint.comp (freeGramRightInverse B) = ContinuousLinearMap.id ℝ V := by
  rw [freeGramRightInverse, ← ContinuousLinearMap.comp_assoc]
  exact (frame_gram_positive_invertible B hB).2.2.self_comp_inverse

/-- The actual inverse Gram operator is self-adjoint, by genuine inverse uniqueness. -/
theorem freeGramInverse_adjoint (B : V →L[ℝ] E) (hB : Function.Injective B) :
    (B.adjoint.comp B).inverse.adjoint = (B.adjoint.comp B).inverse := by
  let G := B.adjoint.comp B
  have hi := (frame_gram_positive_invertible B hB).2.2
  have h1 : G.comp G.inverse.adjoint = ContinuousLinearMap.id ℝ V := by
    have hh := congrArg (fun A : V →L[ℝ] V ↦ A.adjoint) hi.inverse_comp_self
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.adjoint_adjoint] using hh
  have h2 : G.inverse.adjoint.comp G = ContinuousLinearMap.id ℝ V := by
    have hh := congrArg (fun A : V →L[ℝ] V ↦ A.adjoint) hi.self_comp_inverse
    simpa only [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_id,
      ContinuousLinearMap.adjoint_adjoint] using hh
  exact (ContinuousLinearMap.inverse_eq h1 h2).symm

/-- The literal right inverse is the adjoint of the already accepted Gram coefficient map. -/
theorem freeGramRightInverse_adjoint (B : V →L[ℝ] E) (hB : Function.Injective B) :
    freeGramRightInverse B =
      (((B.adjoint.comp B).inverse.comp B.adjoint).adjoint) := by
  rw [ContinuousLinearMap.adjoint_comp, ContinuousLinearMap.adjoint_adjoint,
    freeGramInverse_adjoint B hB]
  rfl

/-- Native smoothness follows from the accepted smooth Gram coefficients and real adjoint map. -/
theorem freeGramRightInverse_contMDiffOn
    {P H M : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [TopologicalSpace H] {I : ModelWithCorners ℝ P H}
    [TopologicalSpace M] [ChartedSpace H M] {s : Set M}
    (B : M → V →L[ℝ] E)
    (hB : ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ B s)
    (hinj : ∀ x ∈ s, Function.Injective (B x)) :
    ContMDiffOn I 𝓘(ℝ, V →L[ℝ] E) ∞ (fun x ↦ freeGramRightInverse (B x)) s := by
  have hc := smooth_frame_gram_coefficients B hB hinj
  let adjEquiv := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := V)
  let adj : (E →L[ℝ] V) →L[ℝ] (V →L[ℝ] E) :=
    adjEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hadj := adj.contDiff.contMDiff.comp_contMDiffOn hc
  apply hadj.congr
  intro x hx
  exact freeGramRightInverse_adjoint (B x) (hinj x hx)

#print axioms freeGramInverse_adjoint
#print axioms freeGramRightInverse_adjoint
#print axioms freeGramRightInverse_spec
#print axioms freeGramRightInverse_contMDiffOn

end GlobalEmbedding.Paper
