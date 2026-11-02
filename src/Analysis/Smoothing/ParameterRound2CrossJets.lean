import Smoothing.ParameterRound2CrossCoordinates

/-!
# Actual full-joint derivative bounds for the repair cross tensor

This is the true bilinear cross of two spatial jet fields. The Leibniz
estimate is applied to their actual functions on an open joint domain.
Neither the desired repair error nor a metric error bound is an input.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set Filter
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
noncomputable section

variable {X D V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup D] [NormedSpace ℝ D]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

private local instance crossJetsTensorSemi : SeminormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance crossJetsTensorNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance crossJetsTensorSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace
private local instance crossJetsPartialSemi : SeminormedAddCommGroup
    ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private local instance crossJetsPartialNormed : NormedAddCommGroup
    ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedAddCommGroup
private local instance crossJetsPartialSpace : NormedSpace ℝ
    ((D →L[ℝ] V) →L[ℝ] D →L[ℝ] D →L[ℝ] ℝ) :=
  ContinuousLinearMap.toNormedSpace

theorem parameterRound2_actual_metric_cross_weighted_jets
    (A B : X → D →L[ℝ] V) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hA : ContDiffOn ℝ ∞ A O) (hB : ContDiffOn ℝ ∞ B O)
    (j : ℕ) (scale KA KB : ℝ) (hscale : 0 ≤ scale) (hKA : 0 ≤ KA) (hKB : 0 ≤ KB)
    (hAb : ∀ r ≤ j, ∀ z ∈ S, scale ^ r * ‖iteratedFDeriv ℝ r A z‖ ≤ KA)
    (hBb : ∀ r ≤ j, ∀ z ∈ S, scale ^ r * ‖iteratedFDeriv ℝ r B z‖ ≤ KB) :
    let R := fun z => actualMetricJetPairing (A z) (B z) + actualMetricJetPairing (B z) (A z)
    ContDiffOn ℝ ∞ R O ∧
      ∀ r ≤ j, ∀ z ∈ S, scale ^ r * ‖iteratedFDeriv ℝ r R z‖ ≤ 2 ^ (j+1) * KA * KB := by
  intro R
  let P : (D →L[ℝ] V) →L[ℝ] (D →L[ℝ] V) →L[ℝ] (D →L[ℝ] D →L[ℝ] ℝ) :=
    actualMetricJetPairing (D := D) (V := V)
  have hab : ContDiffOn ℝ ∞ (fun z => P (A z) (B z)) O :=
    (P.contDiff.comp_contDiffOn hA).clm_apply hB
  have hba : ContDiffOn ℝ ∞ (fun z => P (B z) (A z)) O :=
    (P.contDiff.comp_contDiffOn hB).clm_apply hA
  refine ⟨hab.add hba, ?_⟩
  intro r hr z hz
  have habb := slow_bilinear_jet_bound P actualMetricJetPairing_norm_le O hO A B hA hB
    r scale KA KB hscale hKA z (hSO hz)
    (fun k hk => hAb k (hk.trans hr) z hz) (fun k hk => hBb k (hk.trans hr) z hz)
  have hbab := slow_bilinear_jet_bound P actualMetricJetPairing_norm_le O hO B A hB hA
    r scale KB KA hscale hKB z (hSO hz)
    (fun k hk => hBb k (hk.trans hr) z hz) (fun k hk => hAb k (hk.trans hr) z hz)
  have hfac : (2 : ℝ)^r ≤ 2^j := pow_le_pow_right₀ (by norm_num) hr
  have habb' : scale^r * ‖iteratedFDeriv ℝ r (fun w => P (A w) (B w)) z‖ ≤ 2^j*KA*KB :=
    habb.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hKA) hKB)
  have hbab' : scale^r * ‖iteratedFDeriv ℝ r (fun w => P (B w) (A w)) z‖ ≤ 2^j*KB*KA :=
    hbab.trans (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hfac hKB) hKA)
  have hdab := (hab.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (r : ℕ∞ω) ≤ ∞)
  have hdba := (hba.contDiffAt (hO.mem_nhds (hSO hz))).of_le (by simp : (r : ℕ∞ω) ≤ ∞)
  change scale^r * ‖iteratedFDeriv ℝ r (fun w => P (A w) (B w) + P (B w) (A w)) z‖ ≤ _
  rw [fun_iteratedFDeriv_add_apply hdab hdba]
  calc
    _ ≤ scale^r * (‖iteratedFDeriv ℝ r (fun w => P (A w) (B w)) z‖ +
        ‖iteratedFDeriv ℝ r (fun w => P (B w) (A w)) z‖) :=
      mul_le_mul_of_nonneg_left (norm_add_le _ _) (pow_nonneg hscale _)
    _ ≤ 2^j*KA*KB + 2^j*KB*KA := by nlinarith
    _ = _ := by rw [pow_succ]; ring

#print axioms parameterRound2_actual_metric_cross_weighted_jets
end
end GlobalEmbedding.Continuation
