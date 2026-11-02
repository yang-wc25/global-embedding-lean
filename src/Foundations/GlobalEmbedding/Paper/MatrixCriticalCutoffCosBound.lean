import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual uniform bound for the near-critical part of a cosine period average

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line293.
DAG node: `matrix-critical-cutoff-cos-bound`.
-/

open Set Filter MeasureTheory

namespace GlobalEmbedding.Paper

/-- Compact continuity of the actual amplitude supplies a common constant bounding
the actual near-critical cosine average by the actual critical-cutoff mass.

Proof: bound |a| on the actual compact parameter space times the actual period.
The actual cutoff C=1−smoothTransition(nH²−1) is nonnegative and continuous.
The pointwise norm is at most M·C since |cos|≤1. Native integral norm comparison
and extraction of M prove the estimate. Source: `prop:matrix` cutoff proof. -/
theorem critical_cutoff_cos_bound
    {K : Type*} [TopologicalSpace K] [CompactSpace K]
    (a H : K × ℝ → ℝ) (ha : Continuous a) (hH : Continuous H)
    (φ : K × ℝ → ℝ) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (n : ℕ) (T phase : ℝ) (k : K),
      |∫ t in Icc (0 : ℝ) 1,
        (a (k, t) * (1 - Real.smoothTransition ((n : ℝ) * H (k, t) ^ 2 - 1))) *
          Real.cos (T * φ (k, t) + phase)| ≤
      M * ∫ t in Icc (0 : ℝ) 1,
        1 - Real.smoothTransition ((n : ℝ) * H (k, t) ^ 2 - 1) := by
  obtain ⟨C, hC⟩ := (isCompact_univ.prod isCompact_Icc).exists_bound_of_continuousOn
    ha.continuousOn
  let M := max C 0
  have hM : 0 ≤ M := le_max_right _ _
  refine ⟨M, hM, ?_⟩
  intro n T phase k
  let χ : ℝ → ℝ := fun t ↦ 1 - Real.smoothTransition ((n : ℝ) * H (k, t) ^ 2 - 1)
  have hχ : Continuous χ := by dsimp only [χ]; fun_prop
  have hχnonneg (t : ℝ) : 0 ≤ χ t :=
    sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hmaj : IntervalIntegrable (fun t ↦ M * χ t) volume 0 1 :=
    (continuous_const.mul hχ).intervalIntegrable 0 1
  have hbound := intervalIntegral.norm_integral_le_of_norm_le
    (show (0 : ℝ) ≤ 1 by norm_num) (μ := volume)
    (f := fun t ↦ (a (k, t) * χ t) * Real.cos (T * φ (k, t) + phase))
    (Filter.Eventually.of_forall fun t ht ↦ ?_) hmaj
  · rw [intervalIntegral.integral_const_mul] at hbound
    simpa only [Real.norm_eq_abs, intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
      ← integral_Icc_eq_integral_Ioc] using hbound
  · rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg (hχnonneg t)]
    have hat : |a (k, t)| ≤ M :=
      (hC (k, t) ⟨mem_univ _, (uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht).1.le,
        (uIoc_of_le (show (0 : ℝ) ≤ 1 by norm_num) ▸ ht).2⟩).trans (le_max_left _ _)
    calc
      |a (k, t)| * χ t * |Real.cos (T * φ (k, t) + phase)| ≤
          |a (k, t)| * χ t * 1 :=
        mul_le_mul_of_nonneg_left (Real.abs_cos_le_one _) (mul_nonneg (abs_nonneg _) (hχnonneg t))
      _ = |a (k, t)| * χ t := mul_one _
      _ ≤ M * χ t := mul_le_mul_of_nonneg_right hat (hχnonneg t)

#print axioms critical_cutoff_cos_bound

end GlobalEmbedding.Paper
