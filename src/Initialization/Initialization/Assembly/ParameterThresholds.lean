import Mathlib.Tactic

/-!
# Independent real parameter thresholds for initialization

The conclusion is uniform over every K≥K₀ and every T≥R₀K. It does not replace
the original quantifiers by a selected sequence or a single frequency choice.
-/

namespace GlobalEmbedding.Initialization

/-- Fixed error reserves and a fixed positive tolerance supply two thresholds
before either real frequency is chosen. -/
theorem initialization_error_scale_eventually_small (A ε : ℝ)
    (hA : 0 ≤ A) (hε : 0 < ε) :
    ∃ K₀ R₀ : ℝ, 1 ≤ K₀ ∧ 1 ≤ R₀ ∧
      ∀ K T : ℝ, K₀ ≤ K → R₀ * K ≤ T →
        1 ≤ K ∧ K ≤ T ∧ 0 < T ∧ A * (K⁻¹ + K / T) < ε := by
  let R : ℝ := max 1 (4 * (A+1) / ε)
  have hR : 1 ≤ R := le_max_left _ _
  have hεR : 4 * (A+1) ≤ R * ε :=
    (div_le_iff₀ hε).mp (le_max_right _ _)
  refine ⟨R, R, hR, hR, ?_⟩
  intro K T hK hT
  have hK1 : 1 ≤ K := hR.trans hK
  have hKpos : 0 < K := zero_lt_one.trans_le hK1
  have hKT : K ≤ T := (le_mul_of_one_le_left hKpos.le hR).trans hT
  have hTpos : 0 < T := hKpos.trans_le hKT
  have hεK : 4 * (A+1) ≤ K * ε :=
    hεR.trans (mul_le_mul_of_nonneg_right hK hε.le)
  have hεT : 4 * (A+1) * K ≤ T * ε := by
    calc
      _ ≤ (R * ε) * K := mul_le_mul_of_nonneg_right hεR hKpos.le
      _ = (R * K) * ε := by ring
      _ ≤ T * ε := mul_le_mul_of_nonneg_right hT hε.le
  have hfirst : A / K < ε / 4 := (div_lt_iff₀ hKpos).mpr (by nlinarith)
  have hsecond : (A * K) / T < ε / 4 :=
    (div_lt_iff₀ hTpos).mpr (by nlinarith)
  refine ⟨hK1, hKT, hTpos, ?_⟩
  have heq : A * (K⁻¹ + K / T) = A / K + (A * K) / T := by ring
  rw [heq]
  linarith

end GlobalEmbedding.Initialization
