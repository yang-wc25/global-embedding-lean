import Probes.Round4LinearPhaseBoundedProfiles

/-!
One actual linear phase chart carries its source/target buffers and all
zeroth and positive derivative estimates simultaneously. The same linear
equivalence fixes zero; no equality between independently chosen charts is
assumed. The original quantitative inverse-jet cost is retained as a bound.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

private theorem same_chart_inverse_majorant_base {B : ℝ} (hB : 0 ≤ B) (j : ℕ) :
    B ≤ actualInverseChartMajorant B j := by
  induction j with
  | zero => simp only [actualInverseChartMajorant]; linarith
  | succ j hj =>
    have hpos := actualInverseChartMajorant_one_le hB j
    simp only [actualInverseChartMajorant]
    exact hj.trans (le_add_of_nonneg_right (by positivity))

private theorem same_chart_original_inverse_cost
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M) (j : ℕ) :
    2*actualPhaseInverseConstant mu (2*M) ≤ actualEuclideanPhaseInverseJetCost mu M 0 j := by
  have hInv := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*M by positivity)
  have hB : 0 ≤ slowInverseMajorant (2*actualPhaseInverseConstant mu (2*M)) 0 j :=
    slowInverseMajorant_nonneg (by positivity) le_rfl j
  have hbase : 2*actualPhaseInverseConstant mu (2*M) ≤
      slowInverseMajorant (2*actualPhaseInverseConstant mu (2*M)) 0 j := by
    have h := (slowInverseMajorant_mono (b := 2*actualPhaseInverseConstant mu (2*M))
      (M := 0) le_rfl) (Nat.zero_le j)
    simp only [slowInverseMajorant] at h
    linarith
  have hmaj := same_chart_inverse_majorant_base hB j
  have hnonneg := (zero_le_one.trans (actualInverseChartMajorant_one_le hB j))
  change 2*actualPhaseInverseConstant mu (2*M) ≤
    2^(j+1)*actualInverseChartMajorant
      (slowInverseMajorant (2*actualPhaseInverseConstant mu (2*M)) (2*0) j) j
  simp only [mul_zero]
  exact (hbase.trans hmaj).trans
    (le_mul_of_one_le_left hnonneg (one_le_pow₀ (by norm_num)))

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "X" => Ep × D

theorem round4_actual_linear_phase_same_chart
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (xi : D →L[ℝ] ℝ) (hxi : mu ≤ ‖xi‖) (hxiM : ‖xi‖ ≤ M)
    (z0 : X) (ell : ℝ) (hell : 0 < ell) :
    let r := actualEuclideanPhaseRadius mu M ell
    ∃ b : OpenPartialHomeomorph X X,
      b.source = ball z0 r ∧ b.source ⊆ ball z0 ell ∧ Convex ℝ b.target ∧
      ContDiffOn ℝ ∞ b b.source ∧ ContDiffOn ℝ ∞ b.symm b.target ∧
      (∀ z ∈ b.source, (b z).1 = z.1 ∧ (b z).2 0 = xi z.2) ∧
      (∀ z ∈ b.target, (b.symm z).1 = z.1 ∧ xi (b.symm z).2 = z.2 0) ∧
      closedBall (b z0) (r/(4*actualPhaseInverseConstant mu (2*M))) ⊆ b.target ∧
      (∀ z ∈ b.source, ‖b z‖ ≤ 2*(1+2*M)*‖z‖) ∧
      (∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ 2*(1+2*M)) ∧
      (∀ k, 1 ≤ k → ∀ z ∈ b.source, iteratedFDeriv ℝ (k+1) b z = 0) ∧
      (∀ z ∈ b.target, ‖fderiv ℝ b.symm z‖ ≤ 2*actualPhaseInverseConstant mu (2*M)) ∧
      (∀ k, 1 ≤ k → ∀ z ∈ b.target, iteratedFDeriv ℝ (k+1) b.symm z = 0) ∧
      ∀ (j : ℕ) (weight : ℝ), 0 < weight →
        ∀ k, 1 ≤ k → k ≤ j+1 → ∀ z ∈ b.target,
          weight^(k-1)*‖iteratedFDeriv ℝ k b.symm z‖ ≤ actualEuclideanPhaseInverseJetCost mu M 0 j := by
  intro r
  obtain ⟨L, hL, hLi, hLf, hLinv⟩ := round4_actual_linear_phase_coordinate_equiv
    (Ep := Ep) mu M hmu hM xi hxi hxiM
  have hInv := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*M by positivity)
  have hInvPos : 0 < actualPhaseInverseConstant mu (2*M) := zero_lt_one.trans_le hInv
  have hr : 0 < r := by dsimp [r, actualEuclideanPhaseRadius]; positivity
  have hrle : r ≤ ell := by
    dsimp [r, actualEuclideanPhaseRadius]
    apply (div_le_iff₀ (by positivity : 0 < 4*actualPhaseInverseConstant mu (2*M)*(1+2*M))).mpr
    have hd : 1 ≤ 4*actualPhaseInverseConstant mu (2*M)*(1+2*M) := by nlinarith
    have hmul := mul_le_mul_of_nonneg_left hd hell.le
    nlinarith
  let b := L.toHomeomorph.toOpenPartialHomeomorph.restrOpen (ball z0 r) isOpen_ball
  have hsource : b.source = ball z0 r := by change univ ∩ ball z0 r = _; exact univ_inter _
  have htargetConvex : Convex ℝ b.target := by
    change Convex ℝ (univ ∩ (L.symm ⁻¹' ball z0 r))
    exact convex_univ.inter ((convex_ball z0 r).linear_preimage L.symm.toLinearMap)
  have htarget : closedBall (b z0) (r/(4*actualPhaseInverseConstant mu (2*M))) ⊆ b.target := by
    intro y hy
    change y ∈ univ ∩ (L.symm ⁻¹' ball z0 r)
    refine ⟨mem_univ y, ?_⟩
    change dist (L.symm y) z0 < r
    rw [dist_eq_norm, ← L.symm_apply_apply z0, ← map_sub]
    have hy' : ‖y-L z0‖ ≤ r/(4*actualPhaseInverseConstant mu (2*M)) := by
      change dist y (L z0) ≤ _ at hy
      simpa only [dist_eq_norm] using hy
    calc
      ‖L.symm (y-L z0)‖ ≤ 2*actualPhaseInverseConstant mu (2*M)*‖y-L z0‖ :=
        L.symm.toContinuousLinearMap.le_of_opNorm_le hLinv _
      _ ≤ 2*actualPhaseInverseConstant mu (2*M)*(r/(4*actualPhaseInverseConstant mu (2*M))) :=
        mul_le_mul_of_nonneg_left hy' (by positivity)
      _ = r/2 := by field_simp; ring
      _ < r := by linarith
  have hforward (z : X) : ‖fderiv ℝ b z‖ ≤ 2*(1+2*M) := by
    change ‖fderiv ℝ (L : X →L[ℝ] X) z‖ ≤ _
    rw [ContinuousLinearMap.fderiv]
    exact hLf
  have hinverse (z : X) : ‖fderiv ℝ b.symm z‖ ≤ 2*actualPhaseInverseConstant mu (2*M) := by
    change ‖fderiv ℝ (L.symm : X →L[ℝ] X) z‖ ≤ _
    rw [ContinuousLinearMap.fderiv]
    exact hLinv
  have hhigh (k : ℕ) (hk : 1 ≤ k) (z : X) : iteratedFDeriv ℝ (k+1) b z = 0 :=
    round4_continuous_linear_higher_jet_zero (L : X →L[ℝ] X) k hk z
  have hihigh (k : ℕ) (hk : 1 ≤ k) (z : X) : iteratedFDeriv ℝ (k+1) b.symm z = 0 :=
    round4_continuous_linear_higher_jet_zero (L.symm : X →L[ℝ] X) k hk z
  refine ⟨b, hsource, hsource ▸ ball_subset_ball hrle, htargetConvex, L.contDiff.contDiffOn,
    L.symm.contDiff.contDiffOn, fun z _ => hL z, fun z _ => hLi z, htarget,
    fun z _ => L.toContinuousLinearMap.le_of_opNorm_le hLf z,
    fun z _ => hforward z, fun k hk z _ => hhigh k hk z,
    fun z _ => hinverse z, fun k hk z _ => hihigh k hk z, ?_⟩
  intro j weight hweight k hk hkj z hz
  by_cases hk1 : k = 1
  · subst k
    simp only [Nat.sub_self, pow_zero, one_mul, norm_iteratedFDeriv_one]
    exact (hinverse z).trans (same_chart_original_inverse_cost mu M hmu hM j)
  · obtain ⟨l, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : k ≠ 0)
    rw [hihigh l (by omega) z, norm_zero, mul_zero]
    exact (by positivity : (0 : ℝ) ≤ 2*actualPhaseInverseConstant mu (2*M)).trans
      (same_chart_original_inverse_cost mu M hmu hM j)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_linear_phase_same_chart
