import GlobalEmbedding.Paper.SmoothFrameNormalProjection
import Mathlib.Analysis.InnerProductSpace.EuclideanDist

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Smoothness of actual range-orthogonal projection needs only a finite normed
frame domain, with no inner product on that original domain.

Proof: parametrize the frame domain by a continuous linear equivalence from the
standard finite Euclidean space. The composed frames are smooth and injective, so
the Hilbert-domain theorem applies. Surjectivity of the coordinate equivalence
proves their actual ranges equal the original ranges. Thus the actual projections
are equal; only smoothness is transferred, with no norm estimate or norm replacement.
Source: arbitrary finite-dimensional coordinates in `defn:phase`. -/
theorem smooth_normed_frame_normal_projection
    {X E F : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    {n : ℕ∞ω} {s : Set X} (A : X → E →L[ℝ] F)
    (hA : ContDiffOn ℝ n A s) (hinj : ∀ x ∈ s, Function.Injective (A x)) :
    ContDiffOn ℝ n (fun x ↦ (LinearMap.range (A x).toLinearMap)ᗮ.starProjection) s := by
  let e : EuclideanSpace ℝ (Fin (Module.finrank ℝ E)) ≃L[ℝ] E :=
    ContinuousLinearEquiv.ofFinrankEq (by simp)
  have h := smooth_frame_normal_projection
    (fun x ↦ (A x).comp e.toContinuousLinearMap) (hA.clm_comp contDiffOn_const)
    (fun x hx ↦ (hinj x hx).comp e.injective)
  have hrange (x : X) :
      LinearMap.range ((A x).comp e.toContinuousLinearMap).toLinearMap =
        LinearMap.range (A x).toLinearMap := by
    ext z
    constructor
    · rintro ⟨v, rfl⟩
      exact ⟨e v, rfl⟩
    · rintro ⟨v, rfl⟩
      exact ⟨e.symm v, by simp⟩
  simpa only [hrange] using h

end GlobalEmbedding.Paper
