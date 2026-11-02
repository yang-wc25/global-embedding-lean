import Smoothing.ParameterRound2UniformMeanReserve

/-! The uniform entrance threshold uses only the finite numerical profile
through q*loss. The arbitrary later observation order does not alter it. -/
noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped BigOperators
namespace GlobalEmbedding.Continuation

theorem parameterRound2_uniformMeanProfile_prefix_congr
    (B B' : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (loss i s : ℕ)
    (hB : ∀ k, k ≤ s+i*loss → B k = B' k) :
    parameterRound2_uniformMeanProfile B C loss i s =
      parameterRound2_uniformMeanProfile B' C loss i s := by
  induction i generalizing s with
  | zero => exact hB s (by omega)
  | succ i ih =>
    have hfirst : B s = B' s := hB s (by omega)
    have hrest : parameterRound2_uniformMeanProfile B C loss i (s+loss) =
        parameterRound2_uniformMeanProfile B' C loss i (s+loss) := by
      apply ih
      intro k hk
      apply hB k
      rw [Nat.succ_mul]
      omega
    simp only [parameterRound2_uniformMeanProfile,hfirst,hrest]

theorem parameterRound2_uniformMeanThreshold_prefix_congr
    (B B' : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (rho : ℝ) (q loss : ℕ)
    (hB : ∀ k, k ≤ q*loss → B k = B' k) :
    parameterRound2_uniformMeanThreshold B C rho q loss =
      parameterRound2_uniformMeanThreshold B' C rho q loss := by
  have hsum : (∑ i ∈ Finset.range q, max 0 (C 0 (parameterRound2_uniformMeanProfile B C loss i loss))) =
      ∑ i ∈ Finset.range q, max 0 (C 0 (parameterRound2_uniformMeanProfile B' C loss i loss)) := by
    apply Finset.sum_congr rfl
    intro i hi
    have hiq : i+1 ≤ q := Nat.succ_le_iff.mpr (Finset.mem_range.mp hi)
    have hle : loss+i*loss ≤ q*loss := by
      calc
        loss+i*loss = (i+1)*loss := by ring
        _ ≤ q*loss := Nat.mul_le_mul_right loss hiq
    rw [parameterRound2_uniformMeanProfile_prefix_congr B B' C loss i loss
      (fun k hk => hB k (hk.trans hle))]
  simp only [parameterRound2_uniformMeanThreshold,parameterRound2_uniformMeanEntranceCost,hsum]

theorem parameterRound2_uniformMeanThreshold_finite_prefix
    (B : ℕ → ℝ) (C : ℕ → ℝ → ℝ) (rho : ℝ) (q loss : ℕ) :
    parameterRound2_uniformMeanThreshold B C rho q loss =
      parameterRound2_uniformMeanThreshold (fun s => if s ≤ q*loss then B s else 0) C rho q loss := by
  exact parameterRound2_uniformMeanThreshold_prefix_congr B _ C rho q loss
    (fun k hk => by simp only [ite_eq_left hk])

#print axioms parameterRound2_uniformMeanThreshold_prefix_congr
#print axioms parameterRound2_uniformMeanThreshold_finite_prefix
end GlobalEmbedding.Continuation
