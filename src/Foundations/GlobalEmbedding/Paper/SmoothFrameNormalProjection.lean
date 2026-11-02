import GlobalEmbedding.Paper.NormalProjectionGramFormula
import Mathlib.Analysis.Calculus.ContDiff.Operations

open scoped ContDiff
namespace GlobalEmbedding.Paper
/-- Normal projection depends Cⁿ on any Cⁿ finite-dimensional-source injective frame
family, for every smoothness order, including C∞. The projection is the actual
orthogonal projection and no formula/invertibility is assumed as a hypothesis.

Proof: the real adjoint is continuous linear, Gram is smooth by operator composition,
and actual Gram invertibility gives smooth inverse at every point. Compose the three
operator fields, subtract from identity, and use the proved exact Gram formula.
Source: `defn:phase` and `prop:initialization`, smooth dependence of normal projection. -/
theorem smooth_frame_normal_projection
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {n : ℕ∞ω} {s : Set X} (A : X → E →L[ℝ] F)
    (hsmooth : ContDiffOn ℝ n A s) (hinj : ∀ x ∈ s, Function.Injective (A x)) :
    ContDiffOn ℝ n (fun x ↦ (LinearMap.range (A x).toLinearMap)ᗮ.starProjection) s := by
  let adjEquiv := ContinuousLinearMap.adjoint (𝕜 := ℝ) (E := E) (F := F)
  let adj : (E →L[ℝ] F) →L[ℝ] (F →L[ℝ] E) :=
    adjEquiv.toContinuousLinearEquiv.toContinuousLinearMap
  have hadj : ContDiffOn ℝ n (fun x ↦ (A x).adjoint) s :=
    adj.contDiff.comp_contDiffOn hsmooth
  have hGram := hadj.clm_comp hsmooth
  have hInv : ContDiffOn ℝ n (fun x ↦ ((A x).adjoint.comp (A x)).inverse) s := by
    intro x hx
    have hG := (frame_gram_positive_invertible (A x) (hinj x hx)).2.2
    exact hG.contDiffAt_map_inverse.comp_contDiffWithinAt x (hGram x hx)
  have hR := hsmooth.clm_comp (hInv.clm_comp hadj)
  apply (contDiffOn_const.sub hR).congr
  intro x hx
  exact (normal_projection_gram_formula (A x) (hinj x hx)).2.2.2

end GlobalEmbedding.Paper
