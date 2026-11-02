import GlobalEmbedding.Paper.FrameGramInvertible
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- The actual Gram coefficient operator of a smooth injective frame is smooth
on a manifold, without any uniform spectral-gap hypothesis.

Proof: the real adjoint is continuous linear and composition is smooth, hence the
Gram field is smooth. Actual injectivity gives actual Gram invertibility pointwise.
Smooth inverse calculus at each invertible operator, followed by composition with
the adjoint field, gives the actual coefficient field.
Source: explicit local normal-frame construction expanding `defn:phase`. -/
theorem smooth_frame_gram_coefficients
    {X H B E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
    [TopologicalSpace B] [ChartedSpace H B]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {n : ℕ∞ω} {s : Set B} (A : B → E →L[ℝ] F)
    (hA : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] F) n A s)
    (hinj : ∀ x ∈ s, Function.Injective (A x)) :
    ContMDiffOn I 𝓘(ℝ, F →L[ℝ] E) n
      (fun x ↦ ((A x).adjoint.comp (A x)).inverse.comp (A x).adjoint) s := by
  let adjEquiv := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)
  let adj : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    adjEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hadj : ContMDiffOn I 𝓘(ℝ, F →L[ℝ] E) n (fun x ↦ (A x).adjoint) s := by
    intro x hx
    exact adj.contDiff.comp_contMDiffWithinAt (hA x hx)
  have hGram := hadj.clm_comp hA
  have hInv : ContMDiffOn I 𝓘(ℝ, E →L[ℝ] E) n
      (fun x ↦ ((A x).adjoint.comp (A x)).inverse) s := by
    intro x hx
    have hG := (frame_gram_positive_invertible (A x) (hinj x hx)).2.2
    exact hG.contDiffAt_map_inverse.comp_contMDiffWithinAt
      (f := fun y : B ↦ (A y).adjoint.comp (A y)) (x := x) (hGram x hx)
  exact hInv.clm_comp hadj

end GlobalEmbedding.Paper
