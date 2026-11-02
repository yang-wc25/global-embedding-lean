import Smoothing.ParameterRound2WeightedJetNorms

/-! The actual weighted jet bounds through m+1 produce the original base-one
norm needed by repair. Finiteness is established before taking toReal; the
single inverse-scale factor cancels the literal displacement factor tau. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set
open scoped ContDiff ENNReal BigOperators
namespace GlobalEmbedding.Continuation

theorem actual_paper_base_one_from_weighted_jets
    {ι : Type*} [Fintype ι] {a q : ℕ}
    (m : ℕ) (scale K : ℝ) (hscale : 0 < scale) (hscale1 : scale ≤ 1) (hK : 0 ≤ K)
    (f : ι → (Fin a → ℝ) → Fin q → ℝ) (O S : ι → Set (Fin a → ℝ))
    (hO : ∀ i, IsOpen (O i)) (hSO : ∀ i, S i ⊆ O i)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i))
    (hjet : ∀ i, ∀ k ≤ m+1, ∀ x ∈ S i,
      scale^k*‖iteratedFDeriv ℝ k (f i) x‖ ≤ K) :
    paperAtlasWeighted 1 m scale f O S ≠ ⊤ ∧
      (paperAtlasWeighted 1 m scale f O S).toReal ≤ (m+1)*(K/scale) := by
  have hc (j : ℕ) (hj : j ≤ m) := parameterRound2_paperAtlasCj_le_of_weighted_jets
    (j+1) scale K hscale hscale1 f O S hO hSO hf
      (fun i k hk => hjet i k (by omega))
  have hfinite := parameterRound2_paperAtlasWeighted_finite_of_topOrder 1 m scale f O S
    (ne_top_of_le_ne_top ENNReal.ofReal_ne_top (hc m le_rfl))
  refine ⟨hfinite,?_⟩
  rw [paperAtlasWeighted_toReal 1 m scale hscale.le f O S hfinite]
  calc
    _ ≤ ∑ _j ∈ Finset.range (m+1), K/scale := by
      apply Finset.sum_le_sum
      intro j hj
      have hh := ENNReal.toReal_mono ENNReal.ofReal_ne_top (hc j (by simpa using hj))
      rw [ENNReal.toReal_ofReal (div_nonneg hK (pow_nonneg hscale.le (j+1)))] at hh
      have hp : scale^j*(K/scale^(j+1)) = K/scale := by
        rw [pow_succ]
        field_simp
      exact (mul_le_mul_of_nonneg_left hh (pow_nonneg hscale.le j)).trans_eq hp
    _ = _ := by simp [nsmul_eq_mul]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_paper_base_one_from_weighted_jets
