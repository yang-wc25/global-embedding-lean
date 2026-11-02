import NormalPolar.ConstructionNormalEquiv
import Probes.ActualNormalCompressionResponse

/-!
The same ambient polar construction restricted to the original normal fiber.
`actualNormalInverseSqrt` is the explicit compression of the one analytic
series. It squares to the existing `normalProjectionCompression` inverse;
no separately chosen inverse or identification is introduced.
-/

noncomputable section
namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem normalProjectionCompression_one (K : Submodule ℝ V) :
    normalProjectionCompression K (1 : V →L[ℝ] V) = 1 := by
  ext v
  simp [normalProjectionCompression]

theorem normalProjectionCompression_mul_of_commute (K : Submodule ℝ V)
    (A B : V →L[ℝ] V) (hB : Commute B K.starProjection) :
    normalProjectionCompression K (A * B) =
      normalProjectionCompression K A * normalProjectionCompression K B := by
  ext v
  have hmem : K.starProjection (B (v : V)) = B (v : V) := by
    have h := congrArg (fun T : V →L[ℝ] V ↦ T (v : V)) hB.eq
    simpa only [mul_apply_eq_comp, Submodule.starProjection_mem_subspace_eq_self] using h.symm
  change K.starProjection (A (B (v : V))) =
    K.starProjection (A (K.starProjection (B (v : V))))
  rw [hmem]

theorem normalProjectionCompression_adjoint (K : Submodule ℝ V) (A : V →L[ℝ] V) :
    (normalProjectionCompression K A).adjoint = normalProjectionCompression K A.adjoint := by
  simp only [normalProjectionCompression_eq_adjoint, ContinuousLinearMap.adjoint_comp,
    ContinuousLinearMap.adjoint_adjoint, ContinuousLinearMap.comp_assoc]

theorem normalProjectionCompression_one_sub_defect (K L : Submodule ℝ V) :
    normalProjectionCompression K (1 - projectionDefect K.starProjection L.starProjection) =
      normalProjectionCompression K L.starProjection := by
  have hP : K.starProjection * K.starProjection = K.starProjection := K.isIdempotentElem_starProjection
  have hR : L.starProjection * L.starProjection = L.starProjection := L.isIdempotentElem_starProjection
  have h : K.starProjection * (1 - projectionDefect K.starProjection L.starProjection) *
      K.starProjection = K.starProjection * L.starProjection * K.starProjection := by
    unfold projectionDefect
    noncomm_ring [hP, hR, projection_mul_repeat K.starProjection hP,
      projection_mul_repeat L.starProjection hR]
  ext v
  change K.starProjection ((1 - projectionDefect K.starProjection L.starProjection) (v : V)) =
    K.starProjection (L.starProjection (v : V))
  have hv := congrArg (fun T : V →L[ℝ] V ↦ T (v : V)) h
  simpa only [mul_apply_eq_comp, Submodule.starProjection_mem_subspace_eq_self] using hv

/-- The concrete inverse square root on the original normal fiber. -/
def actualNormalInverseSqrt (K L : Submodule ℝ V) : K →L[ℝ] K :=
  normalProjectionCompression K (actualInvSqrt (projectionDefect K.starProjection L.starProjection))

theorem actualNormalInverseSqrt_selfAdjoint (K L : Submodule ℝ V) :
    IsSelfAdjoint (actualNormalInverseSqrt K L) := by
  change (actualNormalInverseSqrt K L).adjoint = actualNormalInverseSqrt K L
  rw [actualNormalInverseSqrt, normalProjectionCompression_adjoint,
    (actualInvSqrt_selfAdjoint _ (projectionDefect_selfAdjoint _ _
      (isSelfAdjoint_starProjection K) (isSelfAdjoint_starProjection L))).adjoint_eq]

theorem actualNormalInverseSqrt_sq_mul_compression (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    (actualNormalInverseSqrt K L * actualNormalInverseSqrt K L) *
      normalProjectionCompression K L.starProjection = 1 := by
  let E := projectionDefect K.starProjection L.starProjection
  have hE : Commute E K.starProjection :=
    projectionDefect_commute_left _ _ K.isIdempotentElem_starProjection L.isIdempotentElem_starProjection
  have hS : Commute (actualInvSqrt E) K.starProjection := actualInvSqrt_commute E _ hE
  have hI : Commute (1 - E) K.starProjection := (Commute.one_left _).sub_left hE
  change (normalProjectionCompression K (actualInvSqrt E) *
    normalProjectionCompression K (actualInvSqrt E)) *
      normalProjectionCompression K L.starProjection = 1
  rw [← normalProjectionCompression_mul_of_commute K _ _ hS,
    ← normalProjectionCompression_one_sub_defect K L]
  change normalProjectionCompression K (actualInvSqrt E * actualInvSqrt E) *
    normalProjectionCompression K (1 - E) = 1
  rw [← normalProjectionCompression_mul_of_commute K _ _ hI,
    actualInvSqrt_mul_self_one_sub E (norm_sub_sq_lt_one _ _ hclose),
    normalProjectionCompression_one]

theorem actualNormalInverseSqrt_sq_eq_inverse (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    actualNormalInverseSqrt K L * actualNormalInverseSqrt K L =
      (normalProjectionCompression K L.starProjection).inverse := by
  have hc : ‖L.starProjection - K.starProjection‖ < 1 := by rwa [norm_sub_rev]
  obtain ⟨hG, -⟩ := normalProjectionCompression_inverse_bound K L.starProjection
    ‖L.starProjection - K.starProjection‖ hc le_rfl
  have h := congrArg (fun T : K →L[ℝ] K ↦ T * (normalProjectionCompression K L.starProjection).inverse)
    (actualNormalInverseSqrt_sq_mul_compression K L hclose)
  have hGG : normalProjectionCompression K L.starProjection *
      (normalProjectionCompression K L.starProjection).inverse = 1 := hG.self_comp_inverse
  simpa only [mul_assoc, hGG, mul_one, one_mul] using h

theorem actualNormalInverseSqrt_commute_compression (K L : Submodule ℝ V) :
    Commute (actualNormalInverseSqrt K L) (normalProjectionCompression K L.starProjection) := by
  let E := projectionDefect K.starProjection L.starProjection
  have hE : Commute E K.starProjection :=
    projectionDefect_commute_left _ _ K.isIdempotentElem_starProjection L.isIdempotentElem_starProjection
  have hS : Commute (actualInvSqrt E) K.starProjection := actualInvSqrt_commute E _ hE
  have hI : Commute (1 - E) K.starProjection := (Commute.one_left _).sub_left hE
  have hSI : Commute (actualInvSqrt E) (1 - E) :=
    (Commute.one_right _).sub_right (actualInvSqrt_commute E E (Commute.refl E))
  change actualNormalInverseSqrt K L * normalProjectionCompression K L.starProjection =
    normalProjectionCompression K L.starProjection * actualNormalInverseSqrt K L
  rw [← normalProjectionCompression_one_sub_defect K L]
  change normalProjectionCompression K (actualInvSqrt E) * normalProjectionCompression K (1 - E) =
    normalProjectionCompression K (1 - E) * normalProjectionCompression K (actualInvSqrt E)
  rw [← normalProjectionCompression_mul_of_commute K _ _ hI,
    ← normalProjectionCompression_mul_of_commute K _ _ hS, hSI.eq]

theorem actualNormalInverseSqrt_sandwich (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    actualNormalInverseSqrt K L * normalProjectionCompression K L.starProjection *
      actualNormalInverseSqrt K L = 1 := by
  rw [mul_assoc, (actualNormalInverseSqrt_commute_compression K L).symm.eq, ← mul_assoc]
  exact actualNormalInverseSqrt_sq_mul_compression K L hclose

/-- The analytic ambient formula is literally the paper's old-fiber inverse
square root followed by the actual new normal projection. -/
theorem actualPolarOperator_eq_compression_formula (K L : Submodule ℝ V) :
    actualPolarOperator K.starProjection L.starProjection =
      K.subtypeL.comp ((actualNormalInverseSqrt K L).comp
        (K.orthogonalProjectionOnto.comp L.starProjection)) := by
  have hS := actualInvSqrt_projection_commute_left K.starProjection L.starProjection
    K.isIdempotentElem_starProjection L.isIdempotentElem_starProjection
  have hP := K.isIdempotentElem_starProjection
  have h : actualInvSqrt (projectionDefect K.starProjection L.starProjection) *
      K.starProjection * L.starProjection =
      K.starProjection * actualInvSqrt (projectionDefect K.starProjection L.starProjection) *
        K.starProjection * L.starProjection := by
    rw [← hS.eq, mul_assoc _ K.starProjection K.starProjection, hP]
  exact h

end GlobalEmbedding.NormalPolar
