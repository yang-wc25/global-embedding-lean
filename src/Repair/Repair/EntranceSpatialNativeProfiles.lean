import Probes.ActualPhaseEuclideanTransport

/-!
# Actual spatial linear charts followed by original transitions

The linear coordinate equivalence is shared by all parameter charts.
Positive forward jets cost B*T(j); inverse jets cost I^j*T(j).
Order zero uses the real bounded source and its original owner coordinates.
There is no compact maximum over produced charts or derivatives.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation

def repairEntranceSpatialNativeForward (V B : ℝ) (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=0 then B*V else B*T j

def repairEntranceSpatialNativeInverse (V I : ℝ) (T : ℕ → ℝ) (j : ℕ) : ℝ :=
  if j=0 then V else I^j*T j

theorem repairEntranceSpatialNativeForward_nonneg
    {V B : ℝ} {T : ℕ → ℝ} (hV : 0 ≤ V) (hB : 0 ≤ B) (hT : ∀ j, 0 ≤ T j)
    (j : ℕ) : 0 ≤ repairEntranceSpatialNativeForward V B T j := by
  unfold repairEntranceSpatialNativeForward
  split_ifs
  · exact mul_nonneg hB hV
  · exact mul_nonneg hB (hT j)

theorem repairEntranceSpatialNativeInverse_nonneg
    {V I : ℝ} {T : ℕ → ℝ} (hV : 0 ≤ V) (hI : 0 ≤ I) (hT : ∀ j, 0 ≤ T j)
    (j : ℕ) : 0 ≤ repairEntranceSpatialNativeInverse V I T j := by
  unfold repairEntranceSpatialNativeInverse
  split_ifs
  · exact hV
  · exact mul_nonneg (pow_nonneg hI j) (hT j)

theorem repairEntranceSpatialNativeProfiles_congr_prefix (V B I : ℝ)
    (T T' : ℕ → ℝ) (J : ℕ) (h : ∀ j, j ≤ J → T j=T' j) :
    (∀ j, j ≤ J → repairEntranceSpatialNativeForward V B T j=
      repairEntranceSpatialNativeForward V B T' j) ∧
    ∀ j, j ≤ J → repairEntranceSpatialNativeInverse V I T j=
      repairEntranceSpatialNativeInverse V I T' j := by
  constructor <;> intro j hj
  · unfold repairEntranceSpatialNativeForward; rw [h j hj]
  · unfold repairEntranceSpatialNativeInverse; rw [h j hj]

variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]

/-- Exact function identities of the actual native chart, combined with
primitive original-transition jets, produce every native jet. -/
theorem repairEntrance_actual_spatial_linear_profiles
    (b f : OpenPartialHomeomorph X X) (L : X ≃L[ℝ] X)
    (hForward : ∀ z, b z=L (f z)) (hInverse : ∀ z, b.symm z=f.symm (L.symm z))
    (V B I : ℝ) (hV : 0 ≤ V) (hB : 0 ≤ B) (hI : 0 ≤ I)
    (hL : ‖(L : X →L[ℝ] X)‖ ≤ B) (hLi : ‖(L.symm : X →L[ℝ] X)‖ ≤ I)
    (T : ℕ → ℝ) (hT : ∀ j, 0 ≤ T j)
    (hSourceValue : ∀ z ∈ b.source, ‖z‖ ≤ V)
    (hOwnerValue : ∀ z ∈ b.source, ‖f z‖ ≤ V)
    (hForwardJet : ∀ j, 1 ≤ j → ∀ z ∈ b.source, ‖iteratedFDeriv ℝ j f z‖ ≤ T j)
    (hInverseJet : ∀ j, 1 ≤ j → ∀ z ∈ b.target,
      ‖iteratedFDeriv ℝ j f.symm (L.symm z)‖ ≤ T j) :
    (∀ j z, z ∈ b.source → ‖iteratedFDeriv ℝ j b z‖ ≤
      repairEntranceSpatialNativeForward V B T j) ∧
    ∀ j z, z ∈ b.target → ‖iteratedFDeriv ℝ j b.symm z‖ ≤
      repairEntranceSpatialNativeInverse V I T j := by
  have hF : (b : X → X)=L ∘ f := funext hForward
  have hInv : (b.symm : X → X)=f.symm ∘ L.symm := funext hInverse
  constructor
  · intro j z hz
    by_cases hj : j=0
    · subst j
      rw [repairEntranceSpatialNativeForward,if_pos rfl,norm_iteratedFDeriv_zero,hForward]
      exact (L.toContinuousLinearMap.le_of_opNorm_le hL (f z)).trans
        (mul_le_mul_of_nonneg_left (hOwnerValue z hz) hB)
    · rw [repairEntranceSpatialNativeForward,if_neg hj,hF]
      exact (actual_linear_equiv_postcomposition_jet_bound L f j z).trans
        (mul_le_mul hL (hForwardJet j (by omega) z hz) (norm_nonneg _) hB)
  · intro j z hz
    by_cases hj : j=0
    · subst j
      rw [repairEntranceSpatialNativeInverse,if_pos rfl,norm_iteratedFDeriv_zero]
      exact hSourceValue _ (b.map_target hz)
    · rw [repairEntranceSpatialNativeInverse,if_neg hj,hInv]
      calc
        _ ≤ ‖iteratedFDeriv ℝ j f.symm (L.symm z)‖*‖(L.symm : X →L[ℝ] X)‖^j :=
          actual_linear_equiv_precomposition_jet_bound L.symm f.symm j z
        _ ≤ T j*I^j := mul_le_mul (hInverseJet j (by omega) z hz)
          (pow_le_pow_left₀ (norm_nonneg _) hLi j) (by positivity) (hT j)
        _ = I^j*T j := mul_comm _ _

variable {Ep D : Type*} [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
  [NormedAddCommGroup D] [NormedSpace ℝ D]

theorem repairEntrance_identity_prod_linear_norm
    (L : D ≃L[ℝ] D) (B : ℝ) (hB : 1 ≤ B) (hL : ‖(L : D →L[ℝ] D)‖ ≤ B) :
    ‖(((ContinuousLinearEquiv.refl ℝ Ep).prodCongr L) : (Ep × D) →L[ℝ] (Ep × D))‖ ≤ B := by
  apply ContinuousLinearMap.opNorm_le_bound _ (zero_le_one.trans hB)
  intro z
  change ‖(z.1,L z.2)‖ ≤ B*‖z‖
  rw [Prod.norm_def]
  apply max_le
  · exact (norm_fst_le z).trans (by nlinarith [norm_nonneg z])
  · exact (L.toContinuousLinearMap.le_of_opNorm_le hL z.2).trans
      (mul_le_mul_of_nonneg_left (norm_snd_le z) (zero_le_one.trans hB))

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repairEntrance_actual_spatial_linear_profiles
#print axioms GlobalEmbedding.Continuation.repairEntranceSpatialNativeProfiles_congr_prefix
#print axioms GlobalEmbedding.Continuation.repairEntrance_identity_prod_linear_norm
