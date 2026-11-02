import Probes.ActualRepairTargetProfiles

/-! A genuine stage threshold from the uniform finite-mean threshold.
The literal repair scales satisfy all smallness inequalities for every
k >= 10 and both original reserve choices. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
namespace GlobalEmbedding.Continuation

theorem actual_repair_uniform_stage_threshold {epsilon0 : ℝ}
    (he0 : 0 < epsilon0) (he01 : epsilon0 ≤ 1) :
    0 < epsilon0^10 ∧ epsilon0^10 ≤ 1 ∧
    ∀ t : ℝ, 0 < t → t < epsilon0^10 →
      0 < t^(1/10 : ℝ) ∧ t^(1/10 : ℝ) < epsilon0 ∧ t ≤ 1 := by
  refine ⟨pow_pos he0 _,pow_le_one₀ he0.le he01,?_⟩
  intro t ht htt
  have heq : (epsilon0^10)^(1/10 : ℝ) = epsilon0 := by
    rw [← Real.rpow_natCast epsilon0 10, ← Real.rpow_mul he0.le]
    norm_num
  refine ⟨Real.rpow_pos_of_pos ht _,?_,htt.le.trans (pow_le_one₀ he0.le he01)⟩
  exact (Real.rpow_lt_rpow ht.le htt (by norm_num : (0 : ℝ) < 1/10)).trans_eq heq

theorem actual_repair_fixed_scales_admissible {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (k s : ℕ) (hk : 10 ≤ k) (hks : k ≤ s) :
    0 < t^(11/10 : ℝ) ∧ t^(11/10 : ℝ) ≤ t ∧
    t^(1/10 : ℝ)*t^(11/10 : ℝ) = t^(6/5 : ℝ) ∧
    0 < t^k ∧ t^k ≤ t^(1/10 : ℝ)*t^(11/10 : ℝ) ∧
    (t^(6/5 : ℝ))^s ≠ 0 ∧ ((t^(6/5 : ℝ))^s/t^k)^2 ≤ 1 := by
  have hellt := Real.rpow_le_self_of_le_one ht.le ht1 (by norm_num : (1 : ℝ) ≤ 11/10)
  have hprod : t^(1/10 : ℝ)*t^(11/10 : ℝ) = t^(6/5 : ℝ) := by
    rw [← Real.rpow_add ht]
    norm_num
  have hkreal10 : (10 : ℝ) ≤ k := by exact_mod_cast hk
  have hkreal : (6/5 : ℝ) ≤ k := by linarith

  have hd := Real.rpow_le_rpow_of_exponent_ge ht ht1 hkreal
  rw [Real.rpow_natCast] at hd
  exact ⟨Real.rpow_pos_of_pos ht _,hellt,hprod,pow_pos ht _,hprod.symm ▸ hd,
    (pow_pos (Real.rpow_pos_of_pos ht _) _).ne',actual_repair_reserve_square_ratio_le_one ht ht1 k s hks⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_repair_uniform_stage_threshold
#print axioms GlobalEmbedding.Continuation.actual_repair_fixed_scales_admissible
