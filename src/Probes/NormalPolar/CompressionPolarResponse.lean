import NormalPolar.CompressionResponseExplicit
import NormalPolar.ExplicitGapOperator

/-!
# Explicit response of the same actual polar normal identification

The actual formula Qop = i H i* R is differentiated as a product of its
genuine projection family and the already constructed positive H.  Both
terms are retained.  The response correction relative to P DR has an extra
true projection-gap factor, and every reserve coefficient is explicit.
-/

noncomputable section
open Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {V X : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup X] [NormedSpace ℝ X]

private noncomputable local instance polarResponseAmbientSemi :
    SeminormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance polarResponseAmbientNorm :
    NormedAddCommGroup (V →L[ℝ] V) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance polarResponseAmbientSpace :
    NormedSpace ℝ (V →L[ℝ] V) := ContinuousLinearMap.toNormedSpace
private noncomputable local instance polarResponseFiberSemi (K : Submodule ℝ V) :
    SeminormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance polarResponseFiberNorm (K : Submodule ℝ V) :
    NormedAddCommGroup (K →L[ℝ] K) := ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance polarResponseFiberSpace (K : Submodule ℝ V) :
    NormedSpace ℝ (K →L[ℝ] K) := ContinuousLinearMap.toNormedSpace

/-- Differentiability of this same actual Qop follows from its actual
projection family and the constructed positive inverse square root. -/
theorem differentiableAt_actualPolarOperator_of_projection_family
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    DifferentiableAt ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u := by
  simp_rw [actualPolarOperator_eq_compression_formula]
  exact (differentiableAt_const K.subtypeL).clm_comp
    ((differentiableAt_actualNormalInverseSqrt K L u hR hgap).clm_comp
      ((differentiableAt_const K.orthogonalProjectionOnto).clm_comp hR))

/-- The native product rule for the actual ambient Qop.  The current
projection and the derivative of the same positive H both occur. -/
theorem fderiv_actualPolarOperator_compression_apply
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u a =
      (K.subtypeL.comp ((fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u a).comp
        K.orthogonalProjectionOnto)).comp (L u).starProjection +
      (K.subtypeL.comp ((actualNormalInverseSqrt K (L u)).comp
        K.orthogonalProjectionOnto)).comp
          (fderiv ℝ (fun z ↦ (L z).starProjection) u a) := by
  have hH := differentiableAt_actualNormalInverseSqrt K L u hR hgap
  have hprod := (hasFDerivAt_const K.subtypeL u).clm_comp
    (hH.hasFDerivAt.clm_comp ((hasFDerivAt_const K.orthogonalProjectionOnto u).clm_comp hR.hasFDerivAt))
  simp_rw [actualPolarOperator_eq_compression_formula]
  rw [hprod.fderiv]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, add_apply, zero_apply,
    ContinuousLinearMap.compL_apply, ContinuousLinearMap.flip_apply, map_add, map_zero,
    add_zero]
  abel

/-- Subtracting P DR from the genuine derivative leaves the two explicit
normalization corrections. This is an identity, not a response assumption. -/
theorem fderiv_actualPolarOperator_sub_projection_response_eq
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u a -
        K.starProjection.comp (fderiv ℝ (fun z ↦ (L z).starProjection) u a) =
      (K.subtypeL.comp ((fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u a).comp
        K.orthogonalProjectionOnto)).comp (L u).starProjection +
      (K.subtypeL.comp ((actualNormalInverseSqrt K (L u) - 1).comp
        K.orthogonalProjectionOnto)).comp
          (fderiv ℝ (fun z ↦ (L z).starProjection) u a) := by
  rw [fderiv_actualPolarOperator_compression_apply K L u a hR hgap]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, one_apply_eq_self, map_sub]
  change _ + _ - K.starProjection _ = _ + (_ - K.starProjection _)
  abel

/-- The true Q response is bounded by its genuine H response and the
current positive normalization times the true projection response. -/
theorem norm_fderiv_actualPolarOperator_apply_le_compression
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u a‖ ≤
      ‖fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u a‖ +
      ‖actualNormalInverseSqrt K (L u)‖ * ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ := by
  rw [fderiv_actualPolarOperator_compression_apply K L u a hR hgap]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_normalFiberExtension_le K _) (L u).starProjection_norm_le
        (L u).starProjection.opNorm_nonneg (norm_nonneg _)).trans_eq (mul_one _))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalFiberExtension_le K _) (norm_nonneg _))

/-- The correction to P DR is controlled by the native H response and
the quadratic normalization displacement times the native projection response. -/
theorem norm_fderiv_actualPolarOperator_sub_projection_response_le_compression
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (hgap : ‖K.starProjection - (L u).starProjection‖ < 1) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u a -
        K.starProjection.comp (fderiv ℝ (fun z ↦ (L z).starProjection) u a)‖ ≤
      ‖fderiv ℝ (fun z ↦ actualNormalInverseSqrt K (L z)) u a‖ +
      ‖actualNormalInverseSqrt K (L u) - 1‖ * ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ := by
  rw [fderiv_actualPolarOperator_sub_projection_response_eq K L u a hR hgap]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul (norm_normalFiberExtension_le K _) (L u).starProjection_norm_le
        (L u).starProjection.opNorm_nonneg (norm_nonneg _)).trans_eq (mul_one _))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (norm_normalFiberExtension_le K _) (norm_nonneg _))

/-- A fully explicit response bound for the same ambient Qop, with no
compactness-selected derivative constant and no independent Q response input. -/
theorem norm_fderiv_actualPolarOperator_apply_le_explicit
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (q : ℝ) (hq : q < 1) (hgap : ‖K.starProjection - (L u).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u a‖ ≤
      (((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ +
        Real.sqrt ((1 - q ^ 2)⁻¹)) *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ := by
  apply (norm_fderiv_actualPolarOperator_apply_le_compression K L u a hR (hgap.trans_lt hq)).trans
  calc
    _ ≤ ((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ +
        Real.sqrt ((1 - q ^ 2)⁻¹) *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ :=
      add_le_add (norm_fderiv_actualNormalInverseSqrt_apply_le_explicit K L u a hR q hq hgap)
        (mul_le_mul_of_nonneg_right (actualNormalInverseSqrt_norm_le K (L u) q hq hgap)
          (norm_nonneg _))
    _ = _ := by ring

/-- The correction to the leading response P DR is explicitly of order
delta times the true projection response. No commutation of H and DH is used. -/
theorem norm_fderiv_actualPolarOperator_sub_projection_response_le_explicit
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u a : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (q : ℝ) (hq : q < 1) (hgap : ‖K.starProjection - (L u).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u a -
        K.starProjection.comp (fderiv ℝ (fun z ↦ (L z).starProjection) u a)‖ ≤
      (((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ +
        (2 * (1 - q ^ 2))⁻¹ * ‖K.starProjection - (L u).starProjection‖ ^ 2) *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ := by
  apply (norm_fderiv_actualPolarOperator_sub_projection_response_le_compression
    K L u a hR (hgap.trans_lt hq)).trans
  calc
    _ ≤ ((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ +
        (((1 / 2 : ℝ) * (1 - q ^ 2)⁻¹) * ‖K.starProjection - (L u).starProjection‖ ^ 2) *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ :=
      add_le_add (norm_fderiv_actualNormalInverseSqrt_apply_le_explicit K L u a hR q hq hgap)
        (mul_le_mul_of_nonneg_right (actualNormalInverseSqrt_sub_one_norm_le K (L u) q hq hgap)
          (norm_nonneg _))
    _ = _ := by rw [mul_inv_rev]; ring

/-- The explicit estimate for the full native parameter derivative,
including a zero dimensional parameter space. -/
theorem norm_fderiv_actualPolarOperator_le_explicit
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (q : ℝ) (hq : q < 1) (hgap : ‖K.starProjection - (L u).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u‖ ≤
      (((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ +
        Real.sqrt ((1 - q ^ 2)⁻¹)) *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u‖ := by
  have hcoeff : 0 ≤ ((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ +
      Real.sqrt ((1 - q ^ 2)⁻¹) :=
    add_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _)) (Real.sqrt_nonneg _)
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hcoeff (norm_nonneg _))
  intro a
  apply (norm_fderiv_actualPolarOperator_apply_le_explicit K L u a hR q hq hgap).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    ((fderiv ℝ (fun z ↦ (L z).starProjection) u).le_opNorm a) hcoeff

/-- The full derivative correction to P DR has the same explicit extra
projection-gap factor, on the original parameter space. -/
theorem norm_fderiv_actualPolarOperator_sub_projection_response_le_explicit_operator
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (q : ℝ) (hq : q < 1) (hgap : ‖K.starProjection - (L u).starProjection‖ ≤ q) :
    ‖fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u -
        (ContinuousLinearMap.compL ℝ V V V K.starProjection).comp
          (fderiv ℝ (fun z ↦ (L z).starProjection) u)‖ ≤
      (((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ +
        (2 * (1 - q ^ 2))⁻¹ * ‖K.starProjection - (L u).starProjection‖ ^ 2) *
          ‖fderiv ℝ (fun z ↦ (L z).starProjection) u‖ := by
  have hq0 : 0 ≤ q := (norm_nonneg _).trans hgap
  have hq2 : q ^ 2 < 1 := by nlinarith
  have hcoeff : 0 ≤ ((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ +
      (2 * (1 - q ^ 2))⁻¹ * ‖K.starProjection - (L u).starProjection‖ ^ 2 :=
    add_nonneg (mul_nonneg (sq_nonneg _) (norm_nonneg _))
      (mul_nonneg (inv_nonneg.mpr (mul_nonneg (by norm_num) (sub_nonneg.mpr hq2.le)))
        (sq_nonneg _))
  apply ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hcoeff (norm_nonneg _))
  intro a
  apply (norm_fderiv_actualPolarOperator_sub_projection_response_le_explicit
    K L u a hR q hq hgap).trans
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left
    ((fderiv ℝ (fun z ↦ (L z).starProjection) u).le_opNorm a) hcoeff

/-- At equality of the actual normal projections, the first response is
exactly P DR. This requires the displayed actual equality at u; no preferred
parameter center or equality F(t,0)=F0 is assumed. -/
theorem fderiv_actualPolarOperator_eq_projection_response_of_projection_eq
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (u : X)
    (hR : DifferentiableAt ℝ (fun z ↦ (L z).starProjection) u)
    (heq : (L u).starProjection = K.starProjection) :
    fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u =
      (ContinuousLinearMap.compL ℝ V V V K.starProjection).comp
        (fderiv ℝ (fun z ↦ (L z).starProjection) u) := by
  apply sub_eq_zero.mp
  apply norm_eq_zero.mp
  apply le_antisymm _ (norm_nonneg _)
  have h := norm_fderiv_actualPolarOperator_sub_projection_response_le_explicit_operator
    K L u hR 0 (by norm_num) (by simp only [heq, sub_self, norm_zero, le_refl])
  simpa only [heq, sub_self, norm_zero, zero_pow (by decide : 2 ≠ 0),
    mul_zero, add_zero, zero_mul] using h

/-- Uniform validity throughout the given original open parameter domain.
There is no radius reduction or separately chosen family outside a point. -/
theorem norm_fderiv_actualPolarOperator_apply_le_explicit_on
    (K : Submodule ℝ V) (L : X → Submodule ℝ V) (s : Set X) (hs : IsOpen s)
    (hR : DifferentiableOn ℝ (fun z ↦ (L z).starProjection) s)
    (q : ℝ) (hq : q < 1) (hgap : ∀ u ∈ s, ‖K.starProjection - (L u).starProjection‖ ≤ q) :
    ∀ u ∈ s, ∀ a,
      ‖fderiv ℝ (fun z ↦ actualPolarOperator K.starProjection (L z).starProjection) u a‖ ≤
        (((1 - q ^ 2)⁻¹) ^ 2 * ‖K.starProjection - (L u).starProjection‖ +
          Real.sqrt ((1 - q ^ 2)⁻¹)) *
            ‖fderiv ℝ (fun z ↦ (L z).starProjection) u a‖ := by
  intro u hu a
  exact norm_fderiv_actualPolarOperator_apply_le_explicit K L u a
    (hR.differentiableAt (hs.mem_nhds hu)) q hq (hgap u hu)

end GlobalEmbedding.NormalPolar
