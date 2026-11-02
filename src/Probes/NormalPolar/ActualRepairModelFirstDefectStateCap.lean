import NormalPolar.ActualRepairModelFirstDefectScales

/-! A single positive first-scale cap pays the genuine map and tensor
increments. It is chosen from fixed reference/primitive constants, before
actual first maps. The original scales delta=t^10 and tau=t^(6/5) are kept;
no already constructed probe interval is shortened. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
namespace GlobalEmbedding.Continuation

def actualRepairModelFirstDefectStateCap
    (Cref CU CE budget epsilon eta cap : ℝ) : ℝ :=
  min cap (min (1/2) (min (epsilon/(8*(Cref+CU+1)))
    (min (budget/(4*(CU+1)))
      (actualRepairModelFirstDefectInitialCap CE (min eta (budget/2)) 1))))

theorem actualRepairModelFirstDefect_state_cap
    (Cref CU CE budget epsilon eta cap : ℝ)
    (hCref : 0 ≤ Cref) (hCU : 0 ≤ CU) (hbudget : 0 < budget)
    (hepsilon : 0 < epsilon) (heta : 0 < eta) (hcap : 0 < cap) :
    0 < actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta cap ∧
    actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta cap ≤ cap ∧
    actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta cap ≤ 1/2 ∧
    ∀ t : ℝ, 0 < t → t ≤ actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta cap →
      t^((6 : ℝ)/5) ≤ 1/2 ∧
      (t^(10 : ℕ))^2*Cref+CU*t^(10 : ℕ)/t^((6 : ℝ)/5) ≤ (epsilon/4)*(1-t^((6 : ℝ)/5)) ∧
      CU*t^(10 : ℕ)/t^((6 : ℝ)/5) ≤ budget/4 ∧
      CE*(t^(30 : ℝ)+t^((24 : ℝ)/5)) ≤ eta/2 ∧
      CE*(t^(30 : ℝ)+t^((24 : ℝ)/5)) ≤ budget/4 := by
  have heta' : 0 < min eta (budget/2) := lt_min heta (by positivity)
  have herr := actualRepairModelFirstDefect_initial_cap CE (min eta (budget/2)) 1 heta' (by norm_num)
  have hden1 : 0 < 8*(Cref+CU+1) := by positivity
  have hden2 : 0 < 4*(CU+1) := by positivity
  have hc0 : 0 < actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta cap :=
    lt_min hcap (lt_min (by norm_num) (lt_min (div_pos hepsilon hden1)
      (lt_min (div_pos hbudget hden2) herr.1)))
  have hcCap : actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta cap ≤ cap := min_le_left _ _
  have hcHalf : actualRepairModelFirstDefectStateCap Cref CU CE budget epsilon eta cap ≤ 1/2 :=
    (min_le_right _ _).trans (min_le_left _ _)
  refine ⟨hc0,hcCap,hcHalf,?_⟩
  intro t ht htc
  have htHalf : t ≤ 1/2 := htc.trans hcHalf
  have ht1 : t ≤ 1 := htHalf.trans (by norm_num)
  have htmap : t ≤ epsilon/(8*(Cref+CU+1)) :=
    htc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _)))
  have htpair : t ≤ budget/(4*(CU+1)) :=
    htc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))))
  have hterr : t ≤ actualRepairModelFirstDefectInitialCap CE (min eta (budget/2)) 1 :=
    htc.trans ((min_le_right _ _).trans ((min_le_right _ _).trans ((min_le_right _ _).trans (min_le_right _ _))))
  have htau : t^((6 : ℝ)/5) ≤ t := by
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num : (1 : ℝ) ≤ 6/5))
  have hratio : t^(10 : ℕ)/t^((6 : ℝ)/5) ≤ t := by
    rw [GlobalEmbedding.NormalPolar.probe_delta_div_tau_eq_sigma t ht]
    simpa only [Real.rpow_one] using
      (Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num : (1 : ℝ) ≤ 44/5))
  have hpow : (t^(10 : ℕ))^2 ≤ t := by
    rw [← pow_mul]
    simpa only [pow_one] using pow_le_pow_of_le_one ht.le ht1 (by omega : 1 ≤ 10*2)
  have hinc : CU*t^(10 : ℕ)/t^((6 : ℝ)/5) ≤ CU*t := by
    rw [mul_div_assoc]
    exact mul_le_mul_of_nonneg_left hratio hCU
  have hpaymap := (le_div_iff₀ hden1).mp htmap
  have hpaypair := (le_div_iff₀ hden2).mp htpair
  have herrt := herr.2.2.2 t ht hterr
  refine ⟨htau.trans htHalf,?_,?_,?_,?_⟩
  · have hb := add_le_add (mul_le_mul_of_nonneg_right hpow hCref) hinc
    have hsmall : t*Cref+CU*t ≤ epsilon/8 := by nlinarith
    exact (hb.trans hsmall).trans (by nlinarith [htau.trans htHalf])
  · exact hinc.trans (by nlinarith)
  · exact herrt.trans (by have := min_le_left eta (budget/2); linarith)
  · exact herrt.trans (by have := min_le_right eta (budget/2); linarith)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_state_cap
