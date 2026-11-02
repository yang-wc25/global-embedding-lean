import Probes.Round4UniformTemplateLinearPhase

/-!
A genuine global continuous-linear phase coordinate equivalence. This
construction fixes zero, so its zeroth-order chart bound follows from the
original coordinate-value bound. Derivative bounds alone would not control
an arbitrary additive phase constant. All norms retain the native Euclidean
versus max-product conversion factors.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] {m : ℕ}
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Y" => Ep × (ℝ × EuclideanSpace ℝ (Fin m))
local notation "X" => Ep × D

theorem round4_actual_linear_phase_coordinate_equiv
    (mu M : ℝ) (hmu : 0 < mu) (hM : 0 ≤ M)
    (xi : D →L[ℝ] ℝ) (hxi : mu ≤ ‖xi‖) (hxiM : ‖xi‖ ≤ M) :
    ∃ L : X ≃L[ℝ] X,
      (∀ z, (L z).1 = z.1 ∧ (L z).2 0 = xi z.2) ∧
      (∀ z, (L.symm z).1 = z.1 ∧ xi (L.symm z).2 = z.2 0) ∧
      ‖(L : X →L[ℝ] X)‖ ≤ 2*(1+2*M) ∧
      ‖(L.symm : X →L[ℝ] X)‖ ≤ 2*actualPhaseInverseConstant mu (2*M) := by
  have hxi0 : xi ≠ 0 := norm_pos_iff.mp (hmu.trans_le hxi)
  obtain ⟨R, hR⟩ := actual_exists_phase_orientation m xi hxi0
  let C := actualJointEuclideanPhaseEquiv (Ep := Ep) R
  let J := actualJointEuclideanPhaseEquiv (Ep := Ep) (LinearIsometryEquiv.refl ℝ D)
  let d : Y →L[ℝ] ℝ := (xi.comp (ContinuousLinearMap.snd ℝ Ep D)).comp C.symm.toContinuousLinearMap
  have haxisEq : d (0,(1,0)) = ‖xi‖ := by
    change xi (C.symm (0,(1,0))).2 = ‖xi‖
    rw [actualJointEuclideanPhaseEquiv_symm_snd, actualEuclideanPhaseEquiv_symm_axis]
    exact hR
  have hd0 : d (0,(1,0)) ≠ 0 := by rw [haxisEq]; exact (hmu.trans_le hxi).ne'
  have hd : ‖d‖ ≤ 2*M := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    have hy := C.symm.toContinuousLinearMap.le_of_opNorm_le
      (actualJointEuclideanPhaseEquiv_symm_norm R) y
    calc
      ‖d y‖ ≤ ‖xi‖ * ‖(C.symm y).2‖ := xi.le_opNorm _
      _ ≤ M * (2*‖y‖) :=
        mul_le_mul hxiM ((norm_snd_le (C.symm y)).trans hy) (norm_nonneg _) hM
      _ = (2*M)*‖y‖ := by ring
  let T := actualPhaseTriangularEquiv d hd0
  have hT : ‖(T : Y →L[ℝ] Y)‖ ≤ 1+2*M := by
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro y
    change ‖(y.1,(d y,y.2.2))‖ ≤ (1+2*M)*‖y‖
    rw [Prod.norm_def, Prod.norm_def]
    have hbase : ‖y‖ ≤ (1+2*M)*‖y‖ := by nlinarith [norm_nonneg y]
    have hdv : ‖d y‖ ≤ (1+2*M)*‖y‖ :=
      (d.le_opNorm y).trans (mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg _))
    exact max_le ((norm_fst_le y).trans hbase)
      (max_le hdv (((norm_snd_le y.2).trans (norm_snd_le y)).trans hbase))
  have hTi : ‖(T.symm : Y →L[ℝ] Y)‖ ≤ actualPhaseInverseConstant mu (2*M) :=
    actual_phase_inverse_constant_bound mu (2*M) hmu (by positivity) d
      (by rw [haxisEq, abs_of_nonneg (norm_nonneg _)]; exact hxi) hd hd0
  let L := (C.trans T).trans J.symm
  have hforward (z : X) : (L z).1 = z.1 ∧ (L z).2 0 = xi z.2 := by
    refine ⟨rfl, ?_⟩
    change (actualEuclideanPhaseEquiv m).symm (T (C z)).2 0 = xi z.2
    rw [actualEuclideanPhaseEquiv_symm_zero]
    change xi (C.symm (C z)).2 = xi z.2
    rw [C.symm_apply_apply]
  refine ⟨L, hforward, ?_, ?_, ?_⟩
  · intro z
    have hh := hforward (L.symm z)
    rw [L.apply_symm_apply] at hh
    exact ⟨hh.1.symm, hh.2.symm⟩
  · apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    have hCz : ‖C z‖ ≤ ‖z‖ := by
      have hh := C.toContinuousLinearMap.le_of_opNorm_le
        (actualJointEuclideanPhaseEquiv_norm R) z
      change ‖C z‖ ≤ 1*‖z‖ at hh
      rwa [one_mul] at hh
    calc
      ‖L z‖ ≤ 2*‖T (C z)‖ := J.symm.toContinuousLinearMap.le_of_opNorm_le
        (actualJointEuclideanPhaseEquiv_symm_norm (LinearIsometryEquiv.refl ℝ D)) _
      _ ≤ 2*((1+2*M)*‖C z‖) := mul_le_mul_of_nonneg_left
        (T.toContinuousLinearMap.le_of_opNorm_le hT _) (by norm_num)
      _ ≤ 2*((1+2*M)*‖z‖) := mul_le_mul_of_nonneg_left
        (mul_le_mul_of_nonneg_left hCz (by positivity)) (by norm_num)
      _ = (2*(1+2*M))*‖z‖ := by ring
  · have hInvPos : 0 ≤ actualPhaseInverseConstant mu (2*M) :=
      (by norm_num : (0 : ℝ) ≤ 1).trans (actualPhaseInverseConstant_one_le hmu (by positivity))
    apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
    intro z
    have hJz : ‖J z‖ ≤ ‖z‖ := by
      have hh := J.toContinuousLinearMap.le_of_opNorm_le
        (actualJointEuclideanPhaseEquiv_norm (LinearIsometryEquiv.refl ℝ D)) z
      change ‖J z‖ ≤ 1*‖z‖ at hh
      rwa [one_mul] at hh
    calc
      ‖L.symm z‖ ≤ 2*‖T.symm (J z)‖ :=
        C.symm.toContinuousLinearMap.le_of_opNorm_le (actualJointEuclideanPhaseEquiv_symm_norm R) _
      _ ≤ 2*(actualPhaseInverseConstant mu (2*M)*‖J z‖) :=
        mul_le_mul_of_nonneg_left (T.symm.toContinuousLinearMap.le_of_opNorm_le hTi _) (by norm_num)
      _ ≤ 2*(actualPhaseInverseConstant mu (2*M)*‖z‖) :=
        mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hJz hInvPos) (by norm_num)
      _ = (2*actualPhaseInverseConstant mu (2*M))*‖z‖ := by ring

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_actual_linear_phase_coordinate_equiv
