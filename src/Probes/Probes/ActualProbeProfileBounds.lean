import Probes.ActualSourceRestriction

/-! The literal cutoff-times-normal profile has a primitive native slow-jet
budget. This supplies the free part of the same prescribed paired probe. -/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Continuation Set
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {X V : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Actual product jets, retaining the native scalar multiplication norm. -/
theorem actualProbeProfile_weighted_jets
    (chi : X → ℝ) (nu : X → V) (O : Set X) (hO : IsOpen O)
    (hchi : ContDiffOn ℝ ∞ chi O) (hnu : ContDiffOn ℝ ∞ nu O)
    (j : ℕ) (ell Bchi Bnu : ℝ) (hell : 0 ≤ ell)
    (hBchi : 0 ≤ Bchi) (hBnu : 0 ≤ Bnu)
    (hchib : ∀ k ≤ j, ∀ z ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k chi z‖ ≤ Bchi)
    (hnub : ∀ k ≤ j, ∀ z ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k nu z‖ ≤ Bnu) :
    ContDiffOn ℝ ∞ (fun z ↦ chi z • nu z) O ∧
    ∀ k ≤ j, ∀ z ∈ O, ell ^ k * ‖iteratedFDeriv ℝ k (fun y ↦ chi y • nu y) z‖ ≤
      2 ^ j * Bchi * Bnu := by
  refine ⟨hchi.smul hnu, ?_⟩
  intro k hk z hz
  have hbil := slow_bilinear_jet_bound_norm
    (ContinuousLinearMap.lsmul ℝ ℝ : ℝ →L[ℝ] V →L[ℝ] V)
    O hO chi nu hchi hnu k ell Bchi Bnu hell z hz
    (fun a ha ↦ hchib a (ha.trans hk) z hz) (fun a ha ↦ hnub a (ha.trans hk) z hz)
  apply hbil.trans
  apply mul_le_mul_of_nonneg_right _ hBnu
  calc
    _ ≤ 2 ^ k * (1 * Bchi) := mul_le_mul_of_nonneg_left
      (mul_le_mul_of_nonneg_right ContinuousLinearMap.opNorm_lsmul_le hBchi) (by positivity)
    _ ≤ 2 ^ j * Bchi := by
      simpa using mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hk) hBchi

#print axioms actualProbeProfile_weighted_jets
end GlobalEmbedding.Offline
