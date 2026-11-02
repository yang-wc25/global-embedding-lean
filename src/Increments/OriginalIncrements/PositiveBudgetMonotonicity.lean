import IncrementsCompletion.PositiveObserverJets
import Probes.ActualPhaseEuclideanSampleChart

/-!
# Finite numerical upper budgets for the actual positive chart pipeline

Source: `main.tex`, setup:uniform and the last paragraph of lem:increments.
The costs below are the existing actual inverse/composition/observer costs.
These proofs turn finite prefix inequalities, rather than equality of full
profiles, into inequalities of the actual costs.  No zeroth coordinate value,
chart cardinality, sampling enlargement, or extra derivative order is used.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation.OriginalIncrements

theorem positive_prefix_mono
    (P Q : ℕ → ℝ) (j : ℕ)
    (h : ∀ k, 1 ≤ k → k ≤ j → P k ≤ Q k) :
    bufferedTransitionPrefix (incrementsCompletionPositiveSlots P) j ≤
      bufferedTransitionPrefix (incrementsCompletionPositiveSlots Q) j := by
  unfold bufferedTransitionPrefix
  apply add_le_add le_rfl
  apply Finset.sum_le_sum
  intro k hk
  by_cases hk0 : k = 0
  · simp [incrementsCompletionPositiveSlots,hk0]
  · rw [incrementsCompletionPositiveSlots_of_pos P k (by omega),
      incrementsCompletionPositiveSlots_of_pos Q k (by omega)]
    exact h k (by omega) (by simpa using hk)

theorem positive_composition_profile_mono_prefix
    (outer inner outer' inner' : ℕ → ℝ) (j : ℕ)
    (hOuter : ∀ k, 1 ≤ k → 0 ≤ outer k)
    (hInner : ∀ k, 1 ≤ k → 0 ≤ inner k)
    (hO : ∀ k, 1 ≤ k → k ≤ j → outer k ≤ outer' k)
    (hI : ∀ k, 1 ≤ k → k ≤ j → inner k ≤ inner' k) :
    incrementsCompletionPositiveCompositionProfile outer inner j ≤
      incrementsCompletionPositiveCompositionProfile outer' inner' j := by
  have hOp := positive_prefix_mono outer outer' j hO
  have hIp := positive_prefix_mono inner inner' j hI
  have hO0 : 0 ≤ bufferedTransitionPrefix (incrementsCompletionPositiveSlots outer) j :=
    zero_le_one.trans (one_le_bufferedTransitionPrefix
      (incrementsCompletionPositiveSlots_nonneg outer hOuter) j)
  have hI0 : 0 ≤ bufferedTransitionPrefix (incrementsCompletionPositiveSlots inner) j :=
    zero_le_one.trans (one_le_bufferedTransitionPrefix
      (incrementsCompletionPositiveSlots_nonneg inner hInner) j)
  unfold incrementsCompletionPositiveCompositionProfile repairEntranceCompositionProfile
    actualFastChartTransferCost
  apply mul_le_mul _ hOp hO0
  · exact mul_nonneg (by positivity) (pow_nonneg (hI0.trans hIp) j)
  · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hI0 hIp j) (by positivity)

theorem positive_conjugation_profile_mono_prefix
    (NF PF PI NF' PF' PI' : ℕ → ℝ) (j : ℕ)
    (hNF : ∀ k, 1 ≤ k → 0 ≤ NF k)
    (hPF : ∀ k, 1 ≤ k → 0 ≤ PF k)
    (hPI : ∀ k, 1 ≤ k → 0 ≤ PI k)
    (hN : ∀ k, 1 ≤ k → k ≤ j → NF k ≤ NF' k)
    (hF : ∀ k, 1 ≤ k → k ≤ j → PF k ≤ PF' k)
    (hI : ∀ k, 1 ≤ k → k ≤ j → PI k ≤ PI' k) :
    incrementsCompletionPositiveConjugationProfile NF PF PI j ≤
      incrementsCompletionPositiveConjugationProfile NF' PF' PI' j := by
  apply positive_composition_profile_mono_prefix _ _ _ _ j hPF
    (fun k _ => incrementsCompletionPositiveCompositionProfile_nonneg NF PI hNF hPI k) hF
  intro k hk hkj
  exact positive_composition_profile_mono_prefix NF PI NF' PI' k hNF hPI
    (fun l hl hlk => hN l hl (hlk.trans hkj))
    (fun l hl hlk => hI l hl (hlk.trans hkj))

theorem positive_observer_profiles_mono_prefix
    (NF NI Parameter Spatial NF' NI' Parameter' Spatial' : ℕ → ℝ) (j : ℕ)
    (hNF : ∀ k, 1 ≤ k → 0 ≤ NF k) (hNI : ∀ k, 1 ≤ k → 0 ≤ NI k)
    (hParameter : ∀ k, 1 ≤ k → 0 ≤ Parameter k)
    (hSpatial : ∀ k, 1 ≤ k → 0 ≤ Spatial k)
    (hF : ∀ k, 1 ≤ k → k ≤ j → NF k ≤ NF' k)
    (hI : ∀ k, 1 ≤ k → k ≤ j → NI k ≤ NI' k)
    (hP : ∀ k, 1 ≤ k → k ≤ j → Parameter k ≤ Parameter' k)
    (hS : ∀ k, 1 ≤ k → k ≤ j → Spatial k ≤ Spatial' k) :
    incrementsCompletionPositiveObserverForwardProfile NF Parameter Spatial j ≤
      incrementsCompletionPositiveObserverForwardProfile NF' Parameter' Spatial' j ∧
    incrementsCompletionPositiveObserverInverseProfile NI Parameter Spatial j ≤
      incrementsCompletionPositiveObserverInverseProfile NI' Parameter' Spatial' j := by
  have hConj (N : ℕ → ℝ) (hN : ∀ k, 1 ≤ k → 0 ≤ N k) :
      ∀ k, 1 ≤ k → 0 ≤ incrementsCompletionPositiveConjugationProfile N Parameter Parameter k :=
    fun k _ => incrementsCompletionPositiveConjugationProfile_nonneg N Parameter Parameter
      hN hParameter hParameter k
  constructor
  · apply positive_composition_profile_mono_prefix _ _ _ _ j (hConj NF hNF) hSpatial _ hS
    intro k hk hkj
    exact positive_conjugation_profile_mono_prefix NF Parameter Parameter NF' Parameter' Parameter'
      k hNF hParameter hParameter
      (fun l hl hlk => hF l hl (hlk.trans hkj))
      (fun l hl hlk => hP l hl (hlk.trans hkj))
      (fun l hl hlk => hP l hl (hlk.trans hkj))
  · apply positive_composition_profile_mono_prefix _ _ _ _ j hSpatial (hConj NI hNI) hS
    intro k hk hkj
    exact positive_conjugation_profile_mono_prefix NI Parameter Parameter NI' Parameter' Parameter'
      k hNI hParameter hParameter
      (fun l hl hlk => hI l hl (hlk.trans hkj))
      (fun l hl hlk => hP l hl (hlk.trans hkj))
      (fun l hl hlk => hP l hl (hlk.trans hkj))

/-- Monotonicity in the numerical inputs of the actual inverse recurrence,
not merely monotonicity in its iteration index. -/
theorem slowInverseMajorant_mono_values
    {b M b' M' : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hbb : b ≤ b') (hMM : M ≤ M') (j : ℕ) :
    slowInverseMajorant b M j ≤ slowInverseMajorant b' M' j := by
  induction j with
  | zero => exact add_le_add le_rfl hbb
  | succ j hj =>
    have hlo := slowInverseMajorant_nonneg hb hM j
    have hhi := slowInverseMajorant_nonneg (hb.trans hbb) (hM.trans hMM) j
    simp only [slowInverseMajorant]
    apply add_le_add hj
    apply mul_le_mul _ hMM hM
    · exact mul_nonneg (by positivity) (sq_nonneg _)
    · exact mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hlo hj 2) (by positivity)

theorem actualInverseChartMajorant_mono_value
    {B B' : ℝ} (hB : 0 ≤ B) (hBB : B ≤ B') (j : ℕ) :
    actualInverseChartMajorant B j ≤ actualInverseChartMajorant B' j := by
  induction j with
  | zero => exact add_le_add le_rfl hBB
  | succ j hj =>
    have hlo : 0 ≤ actualInverseChartMajorant B j :=
      zero_le_one.trans (actualInverseChartMajorant_one_le hB j)
    have hhi : 0 ≤ actualInverseChartMajorant B' j := hlo.trans hj
    simp only [actualInverseChartMajorant]
    apply add_le_add hj
    exact mul_le_mul (mul_le_mul_of_nonneg_left hBB (by positivity))
      (pow_le_pow_left₀ hlo hj (j+1)) (pow_nonneg hlo _)
      (mul_nonneg (by positivity) (hB.trans hBB))

/-- Only the same-order phase budget is enlarged; the original low-order
noncriticality and two-jet reserves are kept literally unchanged. -/
theorem phase_sample_inverse_cost_mono
    {mu M A B : ℝ} (hmu : 0 < mu) (hM : 0 ≤ M) (hA : 0 ≤ A)
    (hAB : A ≤ B) (j : ℕ) :
    actualEuclideanPhaseSampleInverseJetCost mu M A j ≤
      actualEuclideanPhaseSampleInverseJetCost mu M B j := by
  have hbase : 0 ≤ actualEuclideanPhaseInverseJetCost mu M 0 0 := by
    have hb := actualPhaseInverseConstant_one_le hmu (show 0 ≤ 2*M by positivity)
    simp only [actualEuclideanPhaseInverseJetCost,actualInverseChartMajorant,slowInverseMajorant]
    positivity
  unfold actualEuclideanPhaseSampleInverseJetCost
  exact actualInverseChartMajorant_mono_value
    (slowInverseMajorant_nonneg hbase (mul_nonneg (by positivity) hA) j)
    (slowInverseMajorant_mono_values hbase (mul_nonneg (by positivity) hA) le_rfl
      (mul_le_mul_of_nonneg_left hAB (by positivity)) j) j

end GlobalEmbedding.Continuation.OriginalIncrements

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.positive_observer_profiles_mono_prefix
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.phase_sample_inverse_cost_mono
