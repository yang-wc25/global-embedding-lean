import NormalPolar.ExplicitGapOperator
import NormalPolar.MapFamily

/-!
# A global linear reference gap for the same total normal identification

The total canonical identification satisfies ||Qop-P|| <= 4||P-R|| with
no uniform projection reserve. On the actual half-gap neighborhood it is
the same polar operator and the explicit quadratic correction applies.
Outside that neighborhood every actual isometric identification has ambient
norm at most one. This is a bound relative to the reference projection; it
does not assert global pairwise Lipschitz regularity across the far branch.
-/

noncomputable section

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Any genuine normal-fiber linear isometry, extended using the actual
new projection and old inclusion, has ambient operator norm at most one.
No nonzero-fiber assumption is used. -/
theorem normalEquiv_ambient_norm_le_one
    (K L : Submodule ℝ V) (Q : L ≃ₗᵢ[ℝ] K) :
    ‖K.subtypeL.comp
      (Q.toContinuousLinearEquiv.toContinuousLinearMap.comp L.orthogonalProjectionOnto)‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖Q (L.orthogonalProjectionOnto v)‖ ≤ 1 * ‖v‖
  rw [Q.norm_map, one_mul]
  exact L.norm_orthogonalProjectionOnto_apply_le v

/-- A global linear reference-gap bound for the one actual total canonical
identification. Equal true normal ranks only make that same total field
well-defined; no closeness, reserve or output gap is an assumption. -/
theorem norm_totalNormalPolarEquiv_operator_sub_projection_le_four
    (K L : Submodule ℝ V) (hdim : Module.finrank ℝ L = Module.finrank ℝ K) :
    ‖K.subtypeL.comp
        ((totalNormalPolarEquiv K L hdim).toContinuousLinearEquiv.toContinuousLinearMap.comp
          L.orthogonalProjectionOnto) - K.starProjection‖ ≤
      4 * ‖K.starProjection - L.starProjection‖ := by
  by_cases hsmall : ‖K.starProjection - L.starProjection‖ ≤ (1 / 2 : ℝ)
  · have hclose : ‖K.starProjection - L.starProjection‖ < 1 :=
      hsmall.trans_lt (by norm_num)
    rw [totalNormalPolarEquiv_operator K L hdim hclose]
    have h := norm_actualPolarOperator_sub_projection_le_explicit K L (1 / 2 : ℝ)
      (by norm_num) hsmall
    norm_num at h
    have hnonneg := norm_nonneg (K.starProjection - L.starProjection)
    have hmul := mul_le_mul_of_nonneg_left hsmall hnonneg
    nlinarith
  · have hlarge : (1 / 2 : ℝ) < ‖K.starProjection - L.starProjection‖ := lt_of_not_ge hsmall
    have hbound := (norm_sub_le
      (K.subtypeL.comp
        ((totalNormalPolarEquiv K L hdim).toContinuousLinearEquiv.toContinuousLinearMap.comp
          L.orthogonalProjectionOnto)) K.starProjection).trans
        (add_le_add (normalEquiv_ambient_norm_le_one K L (totalNormalPolarEquiv K L hdim))
          K.starProjection_norm_le)
    linarith

end GlobalEmbedding.NormalPolar
