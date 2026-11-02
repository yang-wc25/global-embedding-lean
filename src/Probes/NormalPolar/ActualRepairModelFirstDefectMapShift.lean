import Probes.ActualOriginalIncrementNormShift

/-! The complete first increment needs the original base-two norm through
order 440, hence actual joint jets through order 442. This conversion keeps
all lower derivatives in each cumulative Cj norm and proves finiteness before
taking real values. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation

theorem actualRepairModelFirstDefect_map_base_from_weighted_jets
    {ι : Type*} [Fintype ι] {a q : ℕ}
    (base j : ℕ) (scale K : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1) (hK : 0 ≤ K)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hjet : ∀ i, ∀ k ≤ j+base, ∀ x ∈ S i,
      scale^k*‖iteratedFDeriv ℝ k (f i) x‖ ≤ K) :
    paperAtlasWeighted base j scale f O S ≠ ⊤ ∧
      (paperAtlasWeighted base j scale f O S).toReal ≤ (j+1)*(K/scale^base) := by
  have hc (k : ℕ) (hk : k ≤ j) := parameterRound2_paperAtlasCj_le_of_weighted_jets
    (k+base) scale K hscale hscale1 f O S hO hSO hf
      (fun i l hl => hjet i l (by omega))
  have hfinite := parameterRound2_paperAtlasWeighted_finite_of_topOrder base j scale f O S
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc j le_rfl))
  refine ⟨hfinite,?_⟩
  rw [paperAtlasWeighted_toReal base j scale hscale.le f O S hfinite]
  calc
    _ ≤ ∑ _k ∈ Finset.range (j+1), K/scale^base := by
      apply Finset.sum_le_sum
      intro k hk
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hc k (by simpa using hk))
      rw [ENNReal.toReal_ofReal (div_nonneg hK (pow_nonneg hscale.le (k+base)))] at hh
      have hp : scale^k*(K/scale^(k+base)) = K/scale^base := by
        rw [pow_add]
        field_simp
      exact (mul_le_mul_of_nonneg_left hh (pow_nonneg hscale.le k)).trans_eq hp
    _ = _ := by simp [nsmul_eq_mul]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actualRepairModelFirstDefect_map_base_from_weighted_jets
