import Probes.ActualPhaseEuclideanModel
import Probes.ActualQuantitativePhaseConstruction

/-!
# Actual Euclidean phase-model transport

An orthogonal orientation is followed by the genuine Euclidean/product split.
The parameter coordinate is unchanged. Native all-order derivative composition
keeps the explicit operator norms, with no isometry asserted for the split.
-/

noncomputable section
open Set Function Filter Metric
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

variable {X Y Z : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]
  [NormedAddCommGroup Z] [NormedSpace ℝ Z]

theorem actual_linear_equiv_precomposition_jet_bound
    (L : X ≃L[ℝ] Y) (f : Y → Z) (k : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ k (f ∘ L) x‖ ≤
      ‖iteratedFDeriv ℝ k f (L x)‖ * ‖(L : X →L[ℝ] Y)‖^k := by
  have he := L.iteratedFDerivWithin_comp_right f uniqueDiffOn_univ (x := x) (mem_univ _) k
  simp only [preimage_univ,iteratedFDerivWithin_univ] at he
  rw [he]
  simpa using (iteratedFDeriv ℝ k f (L x)).norm_compContinuousLinearMap_le
    (fun _ : Fin k => (L : X →L[ℝ] Y))

theorem actual_linear_equiv_postcomposition_jet_bound
    (L : Y ≃L[ℝ] Z) (f : X → Y) (k : ℕ) (x : X) :
    ‖iteratedFDeriv ℝ k (L ∘ f) x‖ ≤ ‖(L : Y →L[ℝ] Z)‖*‖iteratedFDeriv ℝ k f x‖ := by
  rw [L.iteratedFDeriv_comp_left]
  exact ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _

variable {Ep : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]

def actualJointEuclideanPhaseEquiv {m : ℕ}
    (R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1))) :
    (Ep × EuclideanSpace ℝ (Fin (m+1))) ≃L[ℝ]
      (Ep × (ℝ × EuclideanSpace ℝ (Fin m))) :=
  (ContinuousLinearEquiv.refl ℝ Ep).prodCongr
    (R.symm.toContinuousLinearEquiv.trans (actualEuclideanPhaseEquiv m))

@[simp] theorem actualJointEuclideanPhaseEquiv_fst {m : ℕ}
    (R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)))
    (z : Ep × EuclideanSpace ℝ (Fin (m+1))) :
    (actualJointEuclideanPhaseEquiv (Ep := Ep) R z).1 = z.1 := rfl

@[simp] theorem actualJointEuclideanPhaseEquiv_symm_fst {m : ℕ}
    (R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)))
    (z : Ep × (ℝ × EuclideanSpace ℝ (Fin m))) :
    ((actualJointEuclideanPhaseEquiv (Ep := Ep) R).symm z).1 = z.1 := rfl

@[simp] theorem actualJointEuclideanPhaseEquiv_symm_snd {m : ℕ}
    (R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)))
    (z : Ep × (ℝ × EuclideanSpace ℝ (Fin m))) :
    ((actualJointEuclideanPhaseEquiv (Ep := Ep) R).symm z).2 =
      R ((actualEuclideanPhaseEquiv m).symm z.2) := rfl

theorem actualJointEuclideanPhaseEquiv_norm {m : ℕ}
    (R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1))) :
    ‖(actualJointEuclideanPhaseEquiv (Ep := Ep) R :
      (Ep × EuclideanSpace ℝ (Fin (m+1))) →L[ℝ] (Ep × (ℝ × EuclideanSpace ℝ (Fin m))))‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro z
  change ‖(z.1,actualEuclideanPhaseEquiv m (R.symm z.2))‖ ≤ 1*‖z‖
  rw [one_mul,Prod.norm_def]
  apply max_le (norm_fst_le z)
  have hb := (actualEuclideanPhaseEquiv m).toContinuousLinearMap.le_of_opNorm_le
    (actualEuclideanPhaseEquiv_norm m) (R.symm z.2)
  change ‖actualEuclideanPhaseEquiv m (R.symm z.2)‖ ≤ 1*‖R.symm z.2‖ at hb
  rw [one_mul,R.symm.norm_map] at hb
  exact hb.trans (norm_snd_le z)

theorem actualJointEuclideanPhaseEquiv_symm_norm {m : ℕ}
    (R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1))) :
    ‖((actualJointEuclideanPhaseEquiv (Ep := Ep) R).symm :
      (Ep × (ℝ × EuclideanSpace ℝ (Fin m))) →L[ℝ] (Ep × EuclideanSpace ℝ (Fin (m+1))))‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro z
  change ‖(z.1,R ((actualEuclideanPhaseEquiv m).symm z.2))‖ ≤ 2*‖z‖
  rw [Prod.norm_def,R.norm_map]
  apply max_le
  · linarith [norm_fst_le z,norm_nonneg z]
  · have h := (actualEuclideanPhaseEquiv m).symm.toContinuousLinearMap.le_of_opNorm_le
      (actualEuclideanPhaseEquiv_symm_norm m) z.2
    exact h.trans (mul_le_mul_of_nonneg_left (norm_snd_le z) (by norm_num))

theorem actualJointEuclideanPhaseEquiv_inverse_ball {m : ℕ}
    (R : EuclideanSpace ℝ (Fin (m+1)) ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin (m+1)))
    (z0 : Ep × EuclideanSpace ℝ (Fin (m+1))) (ell : ℝ)
    (z : Ep × (ℝ × EuclideanSpace ℝ (Fin m)))
    (hz : z ∈ ball (actualJointEuclideanPhaseEquiv (Ep := Ep) R z0) (ell/2)) :
    (actualJointEuclideanPhaseEquiv (Ep := Ep) R).symm z ∈ ball z0 ell := by
  let C := actualJointEuclideanPhaseEquiv (Ep := Ep) R
  have h := C.symm.toContinuousLinearMap.le_of_opNorm_le
    (actualJointEuclideanPhaseEquiv_symm_norm R) (z-C z0)
  change ‖C.symm (z-C z0)‖ ≤ 2*‖z-C z0‖ at h
  have he : C.symm (z-C z0) = C.symm z-z0 := by rw [map_sub,C.symm_apply_apply]
  rw [he] at h
  have hd : ‖z-C z0‖ < ell/2 := by simpa only [mem_ball,dist_eq_norm] using hz
  rw [mem_ball,dist_eq_norm]
  linarith

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualJointEuclideanPhaseEquiv_norm
#print axioms GlobalEmbedding.Continuation.actualJointEuclideanPhaseEquiv_symm_norm
