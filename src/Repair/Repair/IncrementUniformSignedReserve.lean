import GlobalEmbedding.Offline.FiniteMovingGoodDictionary
import Probes.ActualUniformPhaseTemplateProvider

/-!
# A uniform moving-kernel reserve for the same numerical phase templates

The fixed template API gives a quantitative lower bound on each central
covector and only qualitative Good on its covector ball.  Secondary signed
phases need a quantitative bound on their own, moving kernels.  We obtain
one from the compact set of ALL bounded operators satisfying the central
lower bound.  This set is selected from numerical data before the reference
map, chart family, or parameter family.  No minimum over the current chart
set is taken and the existing template covectors are left unchanged.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
open scoped TensorProduct Topology Classical
namespace GlobalEmbedding.Continuation

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareNS squareAddMonoid squareModule

private local instance incrementReserveRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private local instance incrementReserveSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The numerical bounded central-reserve class, on the literal original
restriction operator and canonical symmetric-square norm. -/
def incrementCentralReserveClass (xi : E →L[ℝ] ℝ) (R c : ℝ) :
    Set (SymmetricSquare E →L[ℝ] V) :=
  {B | ‖B‖ ≤ R ∧ ∀ z, c * ‖z‖ ≤ ‖covectorRestriction B xi z‖}

theorem incrementCentralReserveClass_isCompact (xi : E →L[ℝ] ℝ) (R c : ℝ) :
    IsCompact (incrementCentralReserveClass (V := V) xi R c) := by
  have hclosed : IsClosed {B : SymmetricSquare E →L[ℝ] V |
      ∀ z, c * ‖z‖ ≤ ‖covectorRestriction B xi z‖} := by
    simp only [ofPred_forall]
    apply isClosed_iInter
    intro z
    have hcont : Continuous (fun B : SymmetricSquare E →L[ℝ] V =>
        ‖covectorRestriction B xi z‖) := by
      change Continuous (fun B : SymmetricSquare E →L[ℝ] V =>
        ‖B (symmetricSquareMapL xi.ker.subtypeL z)‖)
      exact (continuous_id.clm_apply continuous_const).norm
    exact isClosed_le continuous_const hcont
  apply (isCompact_closedBall (0 : SymmetricSquare E →L[ℝ] V) R).of_isClosed_subset
    ((isClosed_le continuous_norm continuous_const).inter hclosed)
  intro B hB
  simpa only [Metric.mem_closedBall, dist_zero_right] using (show ‖B‖ ≤ R from hB.1)

/-- A fixed nonzero central covector and numerical operator/lower bounds
produce a single positive moving-covector radius and restriction reserve
for every operator in the entire bounded class. -/
theorem increment_bounded_central_reserve_uniform_moving
    (xi : E →L[ℝ] ℝ) (hxi : xi ≠ 0) (R c : ℝ) (hc : 0 < c) :
    ∃ epsilon mu : ℝ, 0 < epsilon ∧ 0 < mu ∧
      ∀ B : SymmetricSquare E →L[ℝ] V, ‖B‖ ≤ R →
      (∀ z, c * ‖z‖ ≤ ‖covectorRestriction B xi z‖) →
      ∀ eta : E →L[ℝ] ℝ, ‖eta - xi‖ < epsilon →
        LinearSecondFormGoodCovector B.toLinearMap eta.toLinearMap ∧
        (∀ z, mu * ‖z‖ ≤ ‖covectorRestriction B eta z‖) ∧
        ∃ e : SymmetricSquare eta.ker ≃L[ℝ]
            LinearMap.range (covectorRestriction B eta).toLinearMap,
          (∀ z, (e z).val = covectorRestriction B eta z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ mu⁻¹ := by
  classical
  let K := incrementCentralReserveClass (V := V) xi R c
  have hK : IsCompact K := incrementCentralReserveClass_isCompact xi R c
  have hgood (B : K) : LinearSecondFormGoodCovector B.val.toLinearMap xi.toLinearMap := by
    apply (linearSecondFormGoodCovector_iff_native_restriction B.val xi).mpr
    exact ⟨hxi, injective_of_positive_operator_lower_bound
      (E := SymmetricSquare xi.ker) (F := V)
      (covectorRestriction B.val xi) hc B.property.2⟩
  have hlocal (B : K) := actual_good_covector_product_ball_reserves B.val xi (hgood B)
  choose mu hmu eps heps U hU hBU hcontrol using hlocal
  have hcover : K ⊆ ⋃ B : K, U B := by
    intro B hB
    exact mem_iUnion.mpr ⟨⟨B,hB⟩,hBU ⟨B,hB⟩⟩
  obtain ⟨s,hs⟩ := hK.elim_finite_subcover U hU hcover
  obtain ⟨eps0,heps0,heps0le⟩ := finite_positive_common_lower_bound
    (fun B : s => eps B.val) (fun B => heps B.val)
  obtain ⟨mu0,hmu0,hmu0le⟩ := finite_positive_common_lower_bound
    (fun B : s => mu B.val) (fun B => hmu B.val)
  refine ⟨eps0,mu0,heps0,hmu0,?_⟩
  intro B hBR hBc eta heta
  obtain ⟨B0,hB0,hBin⟩ := mem_iUnion₂.mp (hs (show B ∈ K from ⟨hBR,hBc⟩))
  obtain ⟨hg,hlower,e,he,hinv⟩ := hcontrol B0 B hBin eta
    (heta.trans_le (heps0le ⟨B0,hB0⟩))
  refine ⟨hg,?_,e,he,?_⟩
  · intro z
    exact (mul_le_mul_of_nonneg_right (hmu0le ⟨B0,hB0⟩) (norm_nonneg z)).trans (hlower z)
  · exact hinv.trans ((inv_le_inv₀ (hmu B0) hmu0).mpr (hmu0le ⟨B0,hB0⟩))

/-- One radius and one native moving-kernel margin work for an arbitrary
fixed finite list of central covectors, uniformly over the numerical class
of operators. Empty lists are included. -/
theorem increment_finite_bounded_reserve_uniform_moving
    {I : Type*} [Fintype I] (xi : I → E →L[ℝ] ℝ) (hxi : ∀ i, xi i ≠ 0)
    (R c : ℝ) (hc : 0 < c) :
    ∃ epsilon mu : ℝ, 0 < epsilon ∧ 0 < mu ∧
      ∀ B : SymmetricSquare E →L[ℝ] V, ‖B‖ ≤ R →
      ∀ i, (∀ z, c * ‖z‖ ≤ ‖covectorRestriction B (xi i) z‖) →
      ∀ eta : E →L[ℝ] ℝ, ‖eta - xi i‖ < epsilon →
        LinearSecondFormGoodCovector B.toLinearMap eta.toLinearMap ∧
        (∀ z, mu * ‖z‖ ≤ ‖covectorRestriction B eta z‖) ∧
        ∃ e : SymmetricSquare eta.ker ≃L[ℝ]
            LinearMap.range (covectorRestriction B eta).toLinearMap,
          (∀ z, (e z).val = covectorRestriction B eta z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ mu⁻¹ := by
  have hlocal (i : I) := increment_bounded_central_reserve_uniform_moving
    (V := V) (xi i) (hxi i) R c hc
  choose eps mu heps hmu hcontrol using hlocal
  obtain ⟨eps0,heps0,heps0le⟩ := finite_positive_common_lower_bound eps heps
  obtain ⟨mu0,hmu0,hmu0le⟩ := finite_positive_common_lower_bound mu hmu
  refine ⟨eps0,mu0,heps0,hmu0,?_⟩
  intro B hB i hBc eta heta
  obtain ⟨hg,hlower,e,he,hinv⟩ := hcontrol i B hB hBc eta (heta.trans_le (heps0le i))
  refine ⟨hg,?_,e,he,?_⟩
  · intro z
    exact (mul_le_mul_of_nonneg_right (hmu0le i) (norm_nonneg z)).trans (hlower z)
  · exact hinv.trans ((inv_le_inv₀ (hmu i) hmu0).mpr (hmu0le i))

/-- The existing uniform template cover itself supplies quantitative
moving-kernel reserves. The choices depend only on that fixed numerical
cover and the operator bound, not on its subsequently chosen host fields. -/
theorem increment_uniform_template_moving_reserves
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) :
    ∃ epsilon mu : ℝ, 0 < epsilon ∧ 0 < mu ∧
      ∀ B : SymmetricSquare E →L[ℝ] V, ‖B‖ ≤ R →
      ∀ i : C.indices, B ∈ (C.template i).operatorDomain →
      ∀ a (eta : E →L[ℝ] ℝ), ‖eta - (C.template i).covectors a‖ < epsilon →
        LinearSecondFormGoodCovector B.toLinearMap eta.toLinearMap ∧
        (∀ z, mu * ‖z‖ ≤ ‖covectorRestriction B eta z‖) ∧
        ∃ e : SymmetricSquare eta.ker ≃L[ℝ]
            LinearMap.range (covectorRestriction B eta).toLinearMap,
          (∀ z, (e z).val = covectorRestriction B eta z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ mu⁻¹ := by
  classical
  obtain ⟨eps,mu,heps,hmu,hcontrol⟩ := increment_finite_bounded_reserve_uniform_moving
    (V := V) (fun a : C.indices × EdgePair (Module.finrank ℝ E+1) => (C.template a.1).covectors a.2)
    (fun a => (C.template a.1).covectors_ne_zero a.2) R C.restrictionReserve C.restrictionReserve_pos
  refine ⟨eps,mu,heps,hmu,?_⟩
  intro B hB i hi a eta heta
  apply hcontrol B hB (i,a) ?_ eta heta
  intro z
  exact (mul_le_mul_of_nonneg_right (C.bounds i).1 (norm_nonneg z)).trans
    (((C.template i).operator_control B hi a).2.1 z)

/-- A nonzero phase weight does not alter the canonical kernel or its
restriction lower bound. This statement uses the original quotient norm. -/
theorem increment_covector_restriction_lower_smul_iff
    (B : SymmetricSquare E →L[ℝ] V) (xi : E →L[ℝ] ℝ)
    (a mu : ℝ) (ha : a ≠ 0) :
    (∀ z, mu * ‖z‖ ≤ ‖covectorRestriction B (a • xi) z‖) ↔
      (∀ z, mu * ‖z‖ ≤ ‖covectorRestriction B xi z‖) := by
  have hker : (a • xi).ker = xi.ker := by
    change LinearMap.ker (a • xi.toLinearMap) = LinearMap.ker xi.toLinearMap
    exact LinearMap.ker_smul xi.toLinearMap a ha
  let bound (S : Submodule ℝ E) : Prop :=
    ∀ z : SymmetricSquare S, mu * ‖z‖ ≤ ‖B (symmetricSquareMapL S.subtypeL z)‖
  change bound (a • xi).ker ↔ bound xi.ker
  rw [hker]

/-- The same numerical reserve applies to an unnormalized signed phase
whose division by its dominant nonzero weight is in the uniform ball.
This is the form needed by the actual secondary transverse solve. -/
theorem increment_uniform_template_scaled_moving_reserves
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) :
    ∃ epsilon mu : ℝ, 0 < epsilon ∧ 0 < mu ∧
      ∀ B : SymmetricSquare E →L[ℝ] V, ‖B‖ ≤ R →
      ∀ i : C.indices, B ∈ (C.template i).operatorDomain →
      ∀ a (eta : E →L[ℝ] ℝ) (w : ℝ), w ≠ 0 →
      ‖w⁻¹ • eta - (C.template i).covectors a‖ < epsilon →
        LinearSecondFormGoodCovector B.toLinearMap eta.toLinearMap ∧
        (∀ z, mu * ‖z‖ ≤ ‖covectorRestriction B eta z‖) ∧
        ∃ e : SymmetricSquare eta.ker ≃L[ℝ]
            LinearMap.range (covectorRestriction B eta).toLinearMap,
          (∀ z, (e z).val = covectorRestriction B eta z) ∧
          ‖e.symm.toContinuousLinearMap‖ ≤ mu⁻¹ := by
  obtain ⟨eps,mu,heps,hmu,hcontrol⟩ := increment_uniform_template_moving_reserves C R
  refine ⟨eps,mu,heps,hmu,?_⟩
  intro B hB i hi a eta w hw heta
  obtain ⟨hg,hlower,_⟩ := hcontrol B hB i hi a (w⁻¹ • eta) heta
  have hgood : LinearSecondFormGoodCovector B.toLinearMap eta.toLinearMap := by
    exact (linearSecondFormGoodCovector_continuous_smul_iff B.toLinearMap
      eta w⁻¹ (inv_ne_zero hw)).mp hg
  have hlow : ∀ z, mu * ‖z‖ ≤ ‖covectorRestriction B eta z‖ := by
    exact (increment_covector_restriction_lower_smul_iff B eta w⁻¹ mu (inv_ne_zero hw)).mp hlower
  exact ⟨hgood,hlow,inverse_range_norm_le_of_lower_bound
    (E := SymmetricSquare eta.ker) (F := V) (covectorRestriction B eta) hmu hlow⟩

/-- A named radius, selected solely from the fixed numerical template and
operator bound. It is shared by every later source and parameter chart. -/
def incrementUniformSignedRadius
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) : ℝ :=
  min (Classical.choose (increment_uniform_template_scaled_moving_reserves C R)) (C.covectorRadius/2)

/-- The native lower bound selected together with the named radius. -/
def incrementUniformSignedMargin
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) : ℝ :=
  Classical.choose (Classical.choose_spec
    (increment_uniform_template_scaled_moving_reserves C R))

theorem incrementUniformSignedRadius_pos
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) :
    0 < incrementUniformSignedRadius C R :=
  lt_min (Classical.choose_spec (Classical.choose_spec
    (increment_uniform_template_scaled_moving_reserves C R))).1
    (div_pos C.covectorRadius_pos (by norm_num))

theorem incrementUniformSignedRadius_le_half
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) :
    incrementUniformSignedRadius C R ≤ C.covectorRadius/2 := min_le_right _ _

theorem incrementUniformSignedMargin_pos
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ) :
    0 < incrementUniformSignedMargin C R :=
  (Classical.choose_spec (Classical.choose_spec
    (increment_uniform_template_scaled_moving_reserves C R))).2.1

theorem increment_uniform_signed_control
    {K : Set ((SymmetricSquare E →L[ℝ] V) × (E →L[ℝ] E →L[ℝ] ℝ))}
    (C : UniformActualGoodDictionaryCover K) (R : ℝ)
    (B : SymmetricSquare E →L[ℝ] V) (hB : ‖B‖ ≤ R)
    (i : C.indices) (hi : B ∈ (C.template i).operatorDomain)
    (a : EdgePair (Module.finrank ℝ E+1)) (eta : E →L[ℝ] ℝ)
    (w : ℝ) (hw : w ≠ 0)
    (hclose : ‖w⁻¹ • eta - (C.template i).covectors a‖ < incrementUniformSignedRadius C R) :
    LinearSecondFormGoodCovector B.toLinearMap eta.toLinearMap ∧
    (∀ z, incrementUniformSignedMargin C R * ‖z‖ ≤ ‖covectorRestriction B eta z‖) ∧
    ∃ e : SymmetricSquare eta.ker ≃L[ℝ]
        LinearMap.range (covectorRestriction B eta).toLinearMap,
      (∀ z, (e z).val = covectorRestriction B eta z) ∧
      ‖e.symm.toContinuousLinearMap‖ ≤ (incrementUniformSignedMargin C R)⁻¹ :=
  (Classical.choose_spec (Classical.choose_spec
    (increment_uniform_template_scaled_moving_reserves C R))).2.2
    B hB i hi a eta w hw (hclose.trans_le (min_le_left _ _))

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.increment_uniform_template_moving_reserves
#print axioms GlobalEmbedding.Continuation.increment_uniform_template_scaled_moving_reserves
