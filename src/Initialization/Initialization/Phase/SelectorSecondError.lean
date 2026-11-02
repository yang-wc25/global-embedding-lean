import Initialization.Phase.SelectorJetComparison

/-!
# The actual two terms in the second-jet error

The rate covectors are projections of the same actual coframe field. Their
derivatives are computed, not assumed. The exact second-derivative formula
therefore leaves just the derivative of the actual first error and the ambient
first error acted on by a derivative of a genuine selector Hopf column.
-/

noncomputable section
open Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n N : ℕ}

theorem selectorCoframeRates_contDiffAt
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) {x : E}
    (hc : ContDiffAt ℝ ∞ c x) (i : Fin n) :
    ContDiffAt ℝ ∞ (fun y ↦ selectorCoframeRates c y i) x :=
  (((ContinuousLinearMap.compL ℝ E (EuclideanSpace ℝ (Fin n)) ℝ)
    (EuclideanSpace.proj i)).contDiff.contDiffAt).comp x hc

/-- Differentiating an actual coefficient covector is coordinate projection of
the actual derivative of the full coefficient field. -/
theorem selectorCoframeRates_fderiv_apply
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) {x : E}
    (hc : DifferentiableAt ℝ c x) (i : Fin n) (v w : E) :
    fderiv ℝ (fun y ↦ selectorCoframeRates c y i) x v w =
      fderiv ℝ c x v w i := by
  let post := (ContinuousLinearMap.compL ℝ E (EuclideanSpace ℝ (Fin n)) ℝ)
    (EuclideanSpace.proj i)
  have h := post.hasFDerivAt.comp x hc.hasFDerivAt
  have hmap : fderiv ℝ (fun y ↦ selectorCoframeRates c y i) x =
      post.comp (fderiv ℝ c x) := h.fderiv
  rw [hmap]
  rfl

variable (C : Fin n → ℕ) [∀ i, Fact (0 < C i)]
  (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))

theorem selectorSourceMainBilinear_apply
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x v w : E) :
    selectorSourceMainBilinear C S z c x v w =
      ∑ i, c x w i • ∑ j, c x v j • freeHopfDeriv C j (freeHopfDeriv C i S) (z x) := by
  have h := selectorIdealSecondJet_product C S hS (z x) (c x v) (c x w)
  have hL : ContDiffAt ℝ 2 (S ∘ freeHopfOrbitLift C (z x)) 0 :=
    ((hS.comp (freeHopfOrbitLift_contMDiff C (z x))).contDiff.contDiffAt).of_le (by simp)
  rw [selectorIdealSecondJet, coordinateHessianJet_product hL] at h
  exact h

/-- The second tangent term is not a formal tensor: it is the actual derivative
of the same coframe, evaluated against the actual selector first columns. -/
theorem selectorSourceTangentBilinear_apply (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x v w : E) :
    selectorSourceTangentBilinear C S z c x v w =
      ∑ i, fderiv ℝ c x v w i • freeHopfDeriv C i S (z x) :=
  gramFrame_apply _ _

/-- The literal bilinear error is exactly the two actual remainders in the
paper's second-jet argument. No independently specified second jet appears. -/
theorem selectorSourceSecondError_apply
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) {x : E}
    (hz : ContDiffAt ℝ ∞ (selectorSourceAmbient C z) x)
    (hc : ContDiffAt ℝ ∞ c x) (v w : E) :
    selectorSourceSecondError C S z c x v w =
      (∑ i, c x w i •
        fderiv ℝ (selectorAmbientExtension C (freeHopfDeriv C i S))
          (selectorSourceAmbient C z x)
            (selectorSourceAmbientError C z (selectorCoframeRates c) x v)) +
      fderiv ℝ (selectorSourceFirstError C S z (selectorCoframeRates c)) x v w := by
  have h := selectorSource_second_fderiv C S hS z (selectorCoframeRates c) hz
    (selectorCoframeRates_contDiffAt c hc) v w
  simp only [selectorCoframeRates_apply,
    selectorCoframeRates_fderiv_apply c (hc.differentiableAt (by simp))] at h
  simp only [selectorSourceSecondError, ContinuousLinearMap.sub_apply]
  rw [h, selectorSourceMainBilinear_apply C S hS,
    selectorSourceTangentBilinear_apply]
  abel

end GlobalEmbedding.Initialization
