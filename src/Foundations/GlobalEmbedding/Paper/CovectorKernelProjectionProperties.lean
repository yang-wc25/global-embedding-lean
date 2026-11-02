import Mathlib.Analysis.Normed.Operator.BoundedLinearMaps
import GlobalEmbedding.Paper.CovectorKernelProjection
import Mathlib.Analysis.Normed.Operator.ContinuousLinearMap

namespace GlobalEmbedding.Paper

/-- The actual kernel projection varies continuously where its scalar denominator
does not vanish, has image in the actual kernel there, and fixes that kernel.

Proof: continuous evaluation/inverse/scalar multiplication and the bounded
bilinear rank-one operator construction give continuity. Applying ξ cancels the
rank-one correction; on its kernel the correction is zero.
Source: `defn:phase`, actual varying hyperplane minimum. -/
theorem covector_kernel_projection_properties
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (v : E) (ξ0 : E →L[ℝ] ℝ) (h0 : ξ0 v ≠ 0) :
    ContinuousAt (covectorKernelProjection v) ξ0 ∧
    (∀ (ξ : E →L[ℝ] ℝ), ξ v ≠ 0 → ∀ w : E, ξ (covectorKernelProjection v ξ w) = 0) ∧
    (∀ (ξ : E →L[ℝ] ℝ) (w : E), ξ w = 0 → covectorKernelProjection v ξ w = w) := by
  have he : Continuous (fun ξ : E →L[ℝ] ℝ ↦ ξ v) :=
    continuous_id.clm_apply continuous_const
  have hv : ContinuousAt (fun ξ : E →L[ℝ] ℝ ↦ (ξ v)⁻¹ • v) ξ0 :=
    (he.continuousAt.inv₀ h0).smul continuousAt_const
  have hc : ContinuousAt (covectorKernelProjection v) ξ0 := by
    change ContinuousAt (fun ξ : E →L[ℝ] ℝ ↦ ContinuousLinearMap.id ℝ E -
      (ContinuousLinearMap.smulRightL ℝ E E ξ) ((ξ v)⁻¹ • v)) ξ0
    exact continuousAt_const.sub ((ContinuousLinearMap.smulRightL ℝ E E).continuous.continuousAt.clm_apply hv)
  refine ⟨hc, ?_, ?_⟩
  · intro ξ hξ w
    simp only [covectorKernelProjection, sub_apply, ContinuousLinearMap.id_apply,
      ContinuousLinearMap.smulRight_apply, map_sub, map_smul, smul_eq_mul]
    rw [inv_mul_cancel₀ hξ, mul_one, sub_self]
  · intro ξ w hw
    simp [covectorKernelProjection, hw]

end GlobalEmbedding.Paper
