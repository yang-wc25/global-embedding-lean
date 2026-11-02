import Smoothing.ParameterRound2NormAlgebra

/-!
# Choosing the actual initial scale from finite reference jets

The original weighted norm tends to its unweighted base norm as t tends to
zero. Here an explicit linear bound proves this using only the finite top
reference jet. The map base is 2 and the tensor base is 0, so m=440 costs
exactly map442 and tensor440. No target metric enters this scale choice.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {ι : Type*} [Fintype ι] {a q q' : ℕ}

/-- Positive weighted derivative levels are bounded by t times the true top
order norm. The base level is retained exactly. -/
theorem parameterRound2_paperAtlasWeighted_le_base_add_top
    (base m : ℕ) {t : ℝ} (ht : 0 ≤ t) (ht1 : t ≤ 1)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hfinite : paperAtlasCj (m + base) f O S ≠ ⊤) :
    (paperAtlasWeighted base m t f O S).toReal ≤
      (paperAtlasCj base f O S).toReal +
        t * m * (paperAtlasCj (m + base) f O S).toReal := by
  have hweighted := parameterRound2_paperAtlasWeighted_finite_of_topOrder base m t f O S hfinite
  rw [paperAtlasWeighted_toReal base m t ht f O S hweighted, Finset.sum_range_succ']
  simp only [pow_zero, zero_add, one_mul]
  have hs : (∑ j ∈ Finset.range m, t ^ (j + 1) * (paperAtlasCj (j + 1 + base) f O S).toReal) ≤
      ∑ _j ∈ Finset.range m, t * (paperAtlasCj (m + base) f O S).toReal := by
    apply Finset.sum_le_sum
    intro j hj
    have hpower : t ^ (j + 1) ≤ t := by
      rw [pow_succ]
      simpa only [one_mul] using mul_le_mul_of_nonneg_right (pow_le_one₀ ht ht1) ht
    have hnorm := ENNReal.toReal_mono hfinite
      (parameterRound2_paperAtlasCj_mono_order
        (show j + 1 + base ≤ m + base by have := Finset.mem_range.mp hj; omega) f O S)
    exact mul_le_mul hpower hnorm ENNReal.toReal_nonneg ht
  calc
    _ ≤ (∑ _j ∈ Finset.range m, t * (paperAtlasCj (m + base) f O S).toReal) +
        (paperAtlasCj base f O S).toReal := add_le_add hs le_rfl
    _ = _ := by simp [nsmul_eq_mul]; ring

/-- The scale is chosen from the reference map/tensor only and works for all
smaller positive scales. m=440 has the literal map442/tensor440 entrance. -/
theorem parameterRound2_exists_reference_pair_scale
    (m : ℕ) (f : ι → (Fin a → ℝ) → Fin q → ℝ)
    (g : ι → (Fin a → ℝ) → Fin q' → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hfFinite : paperAtlasCj (m + 2) f O S ≠ ⊤)
    (hgFinite : paperAtlasCj m g O S ≠ ⊤)
    (budget cap : ℝ) (hcap : 0 < cap)
    (hbudget : 4 * ((paperAtlasCj 2 f O S).toReal + (paperAtlasCj 0 g O S).toReal) < budget) :
    ∃ t0 : ℝ, 0 < t0 ∧ t0 ≤ 1 ∧ t0 ≤ cap ∧
      ∀ t : ℝ, 0 ≤ t → t ≤ t0 →
        (paperAtlasWeighted 2 m t f O S).toReal +
          (paperAtlasWeighted 0 m t g O S).toReal ≤ budget / 2 := by
  let R := (paperAtlasCj 2 f O S).toReal + (paperAtlasCj 0 g O S).toReal
  let T := (m : ℝ) * ((paperAtlasCj (m+2) f O S).toReal + (paperAtlasCj m g O S).toReal)
  have hR : 0 ≤ R := add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg
  have hT : 0 ≤ T := mul_nonneg (Nat.cast_nonneg _) (add_nonneg ENNReal.toReal_nonneg ENNReal.toReal_nonneg)
  have hb : 0 < budget := lt_of_le_of_lt (mul_nonneg (by norm_num) hR) hbudget
  have hmargin : 0 < budget / 2 - R := by dsimp only [R]; linarith
  let t0 := min cap (min 1 ((budget / 2 - R) / (1 + T)))
  have ht0 : 0 < t0 := lt_min hcap (lt_min zero_lt_one (div_pos hmargin (by linarith)))
  refine ⟨t0, ht0, (min_le_right _ _).trans (min_le_left _ _), min_le_left _ _, ?_⟩
  intro t ht htt
  have ht1 : t ≤ 1 := htt.trans ((min_le_right _ _).trans (min_le_left _ _))
  have hbound : t * (1 + T) ≤ budget / 2 - R := by
    apply (le_div_iff₀ (by linarith : 0 < 1 + T)).mp
    exact htt.trans ((min_le_right _ _).trans (min_le_right _ _))
  have hf := parameterRound2_paperAtlasWeighted_le_base_add_top 2 m ht ht1 f O S hfFinite
  have hg := parameterRound2_paperAtlasWeighted_le_base_add_top 0 m ht ht1 g O S (by simpa using hgFinite)
  have hm : t * T ≤ budget / 2 - R := by nlinarith
  dsimp only [T, R] at hm
  simp only [Nat.add_zero] at hg
  nlinarith

#print axioms parameterRound2_paperAtlasWeighted_le_base_add_top
#print axioms parameterRound2_exists_reference_pair_scale
end
end GlobalEmbedding.Continuation
