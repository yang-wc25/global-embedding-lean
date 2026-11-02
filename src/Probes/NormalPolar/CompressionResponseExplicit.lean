import NormalPolar.CompressionResponseDefect
import NormalPolar.SylvesterNorm

/-!
# An explicit quadratic-normalization response constant for the actual H

The same constructed H has a self-adjoint native derivative and satisfies
its proved Sylvester identity. The actual compression's derivative carries
the true projection-gap factor. Combining the coercive Sylvester estimate
with the true quadratic inverse reserve gives a numerical constant, with
no compactness-selected derivative bound or response premise.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Offline GlobalEmbedding.Continuation

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]

private noncomputable local instance explicitResponseAmbientSemi :
    SeminormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance explicitResponseAmbientNorm :
    NormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance explicitResponseAmbientSpace :
    NormedSpace ℝ (V →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance explicitResponseFiberSemi (K : Submodule ℝ V) :
    SeminormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance explicitResponseFiberNorm (K : Submodule ℝ V) :
    NormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance explicitResponseFiberSpace (K : Submodule ℝ V) :
    NormedSpace ℝ (K →L[ℝ] K) := ContinuousLinearMap.toNormedSpace

/-- A fully numerical native response estimate for the same actual positive
inverse square root. The constant and the actual projection gap stay separate.
No commutation of H and its response is assumed. -/
theorem norm_fderiv_actualNormalInverseSqrt_apply_le_explicit
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (q : ℝ) (hq : q < 1) (hgap : ‖K.starProjection - (L u).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u a‖ ≤
      ((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ *
        ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ := by
  let H := actualNormalInverseSqrt K (L u)
  let DH := fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u a
  let G := normalProjectionCompression K (L u).starProjection
  let DG := normalProjectionCompression K
    (fderiv ℝ (fun z ↦ (L z).starProjection) u a)
  let gap := ‖K.starProjection - (L u).starProjection‖
  let response := ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖
  let reserve := (1 - q ^ 2)⁻¹
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hgap
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hreserve : 0 ≤ reserve := inv_nonneg.mpr (sub_nonneg.mpr hq2.le)
  have hclose : ‖K.starProjection - (L u).starProjection‖ < 1 := hgap.trans_lt hq
  have hDH : IsSelfAdjoint DH := fderiv_actualNormalInverseSqrt_selfAdjoint K L u a hR hclose
  have hsylvester : ‖DH‖ ≤ ‖H * DH + DH * H‖ / 2 :=
    norm_selfAdjoint_le_half_actualNormalInverseSqrt_sylvester K (L u) hclose DH hDH
  have hidentity : H * DH + DH * H = -(G.inverse * DG * G.inverse) := by
    exact (add_comm _ _).trans (fderiv_actualNormalInverseSqrt_sylvester K L u a hR hclose)
  have hGinv : ‖G.inverse‖ ≤ reserve :=
    (normalProjectionCompression_inverse_quadratic_bound K (L u) q hq hgap).2
  have hDG : ‖DG‖ ≤ 2 * gap * response := by
    have h := norm_fderiv_actualNormalCompression_apply_le_gap K L u a hR
    rw [fderiv_normalProjectionCompression_apply K (fun z ↦ (L z).starProjection) u a hR] at h
    exact h
  calc
    ‖DH‖ ≤ ‖H * DH + DH * H‖ / 2 := hsylvester
    _ = ‖G.inverse * DG * G.inverse‖ / 2 := by rw [hidentity, norm_neg]
    _ ≤ ((‖G.inverse‖ * ‖DG‖) * ‖G.inverse‖) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      exact (norm_mul_le (G.inverse * DG) G.inverse).trans
        (mul_le_mul_of_nonneg_right (norm_mul_le G.inverse DG) (norm_nonneg G.inverse))
    _ ≤ ((reserve * (2 * gap * response)) * reserve) / 2 := by
      apply div_le_div_of_nonneg_right _ (by norm_num)
      apply mul_le_mul (mul_le_mul hGinv hDG (norm_nonneg _) hreserve) hGinv (norm_nonneg _)
      exact mul_nonneg hreserve (mul_nonneg (mul_nonneg (by norm_num) (norm_nonneg _)) (norm_nonneg _))
    _ = _ := by dsimp only [reserve, gap, response]; ring

/-- The same estimate for the full native derivative operator. -/
theorem norm_fderiv_actualNormalInverseSqrt_le_explicit
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (q : ℝ) (hq : q < 1) (hgap : ‖K.starProjection - (L u).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u‖ ≤
      ((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ *
        ‖fderiv ℝ (fun z ↦ (L z).starProjection) u‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _
    (mul_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (norm_nonneg _))
  intro a
  apply (norm_fderiv_actualNormalInverseSqrt_apply_le_explicit K L u a hR q hq hgap).trans
  have h := mul_le_mul_of_nonneg_left
    ((fderiv ℝ (fun z ↦ (L z).starProjection) u).le_opNorm a)
    (mul_nonneg (sq_nonneg ((1 - q ^ 2)⁻¹)) (norm_nonneg (K.starProjection - (L u).starProjection)))
  simpa only [mul_assoc] using h

/-- At equality of the true old and current projections the normalization
has zero first parameter response. This is a consequence of the same native
formula and its quadratic correction, not a separate choice at the diagonal. -/
theorem fderiv_actualNormalInverseSqrt_eq_zero_of_projection_eq
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (heq : (L u).starProjection = K.starProjection) :
    fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u = 0 := by
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := norm_fderiv_actualNormalInverseSqrt_le_explicit K L u hR 0 (by norm_num)
    (by simp only [heq, sub_self, norm_zero, le_refl])
  simpa only [heq, sub_self, norm_zero, mul_zero, zero_mul] using h

end GlobalEmbedding.NormalPolar
