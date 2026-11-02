import NormalPolar.InverseSqrtQuantitative

/-!
# An explicit same-polar-operator gap with linear coefficient one

The actual old-fiber inverse square root supplies the quadratic correction.
Inclusion and true orthogonal projection are contractions even when the normal
fiber is zero dimensional. The remaining linear term is the genuine moving
projection difference. No compactness-selected gap constant is used here.
-/

noncomputable section

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Extending an operator on the actual old normal fiber by the genuine
projection and inclusion does not increase its norm, including the zero fiber. -/
theorem norm_normalFiberExtension_le
    (K : Submodule ℝ V) (H : K →L[ℝ] K) :
    ‖K.subtypeL.comp (H.comp K.orthogonalProjectionOnto)‖ ≤ ‖H‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg H)
  intro v
  change ‖H (K.orthogonalProjectionOnto v)‖ ≤ ‖H‖ * ‖v‖
  exact (H.le_opNorm _).trans (mul_le_mul_of_nonneg_left
    (K.norm_orthogonalProjectionOnto_apply_le v) (norm_nonneg H))

/-- Exact decomposition of the same explicit Qop into the positive
normalization correction and the genuine projection displacement. -/
theorem actualPolarOperator_sub_projection_eq_corrections
    (K L : Submodule ℝ V) :
    actualPolarOperator K.starProjection L.starProjection - K.starProjection =
      (K.subtypeL.comp ((actualNormalInverseSqrt K L - 1).comp
        K.orthogonalProjectionOnto)).comp L.starProjection +
      K.starProjection.comp (L.starProjection - K.starProjection) := by
  rw [actualPolarOperator_eq_compression_formula]
  apply ContinuousLinearMap.ext
  intro v
  simp only [ContinuousLinearMap.comp_apply, sub_apply, add_apply, one_apply_eq_self, map_sub]
  change ((actualNormalInverseSqrt K L (K.orthogonalProjectionOnto (L.starProjection v)) : K) : V) -
      K.starProjection v =
    (((actualNormalInverseSqrt K L (K.orthogonalProjectionOnto (L.starProjection v)) : K) : V) -
      K.starProjection (L.starProjection v)) +
      (K.starProjection (L.starProjection v) - K.starProjection (K.starProjection v))
  have hPP : K.starProjection (K.starProjection v) = K.starProjection v :=
    congrArg (fun T : V →L[ℝ] V ↦ T v) K.isIdempotentElem_starProjection
  rw [hPP]
  abel

/-- The compression correction and true projection gap bound the same Qop.
All factors have norm at most one; no nonzero-fiber assumption is needed. -/
theorem norm_actualPolarOperator_sub_projection_le_compression
    (K L : Submodule ℝ V) :
    ‖actualPolarOperator K.starProjection L.starProjection - K.starProjection‖ ≤
      ‖K.starProjection - L.starProjection‖ + ‖actualNormalInverseSqrt K L - 1‖ := by
  rw [actualPolarOperator_sub_projection_eq_corrections]
  have hcorrection :
      ‖(K.subtypeL.comp ((actualNormalInverseSqrt K L - 1).comp
        K.orthogonalProjectionOnto)).comp L.starProjection‖ ≤ ‖actualNormalInverseSqrt K L - 1‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    exact (mul_le_mul (norm_normalFiberExtension_le K _) L.starProjection_norm_le
      L.starProjection.opNorm_nonneg (actualNormalInverseSqrt K L - 1).opNorm_nonneg).trans_eq (mul_one _)
  have hprojection : ‖K.starProjection.comp (L.starProjection - K.starProjection)‖ ≤
      ‖K.starProjection - L.starProjection‖ := by
    apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
    rw [norm_sub_rev]
    exact (mul_le_mul_of_nonneg_right K.starProjection_norm_le (norm_nonneg _)).trans_eq (one_mul _)
  exact (norm_add_le _ _).trans ((add_le_add hcorrection hprojection).trans_eq (add_comm _ _))

/-- An explicit same-Q gap on the original true projection reserve. The
linear coefficient is exactly one and the correction is explicitly quadratic. -/
theorem norm_actualPolarOperator_sub_projection_le_explicit
    (K L : Submodule ℝ V) (q : ℝ) (hq : q < 1)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ q) :
    ‖actualPolarOperator K.starProjection L.starProjection - K.starProjection‖ ≤
      ‖K.starProjection - L.starProjection‖ +
        (2 * (1 - q ^ 2))⁻¹ * ‖K.starProjection - L.starProjection‖ ^ 2 := by
  apply (norm_actualPolarOperator_sub_projection_le_compression K L).trans
  calc
    _ ≤ ‖K.starProjection - L.starProjection‖ +
        ((1 / 2 : ℝ) * (1 - q ^ 2)⁻¹) * ‖K.starProjection - L.starProjection‖ ^ 2 :=
      add_le_add le_rfl (actualNormalInverseSqrt_sub_one_norm_le K L q hq hgap)
    _ = _ := by rw [mul_inv_rev]; ring

/-- The explicit estimate belongs to the actual orthogonal normal
identification, not merely an independently named ambient expression. -/
theorem norm_actualNormalPolarEquiv_operator_sub_projection_le_explicit
    (K L : Submodule ℝ V) (q : ℝ) (hq : q < 1)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ q) :
    ‖K.subtypeL.comp
        ((actualNormalPolarEquiv K L (hgap.trans_lt hq)).toContinuousLinearEquiv.toContinuousLinearMap.comp
          L.orthogonalProjectionOnto) - K.starProjection‖ ≤
      ‖K.starProjection - L.starProjection‖ +
        (2 * (1 - q ^ 2))⁻¹ * ‖K.starProjection - L.starProjection‖ ^ 2 := by
  rw [actualNormalPolarEquiv_operator]
  exact norm_actualPolarOperator_sub_projection_le_explicit K L q hq hgap

end GlobalEmbedding.NormalPolar
