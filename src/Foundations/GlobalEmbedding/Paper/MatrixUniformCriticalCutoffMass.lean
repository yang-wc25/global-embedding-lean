import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.UniformSpace.Dini

/-!
# Uniform smallness of actual critical-region cutoff averages

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
line 293; the cutoff proof is also recorded in the `prop-matrix` DAG node.
DAG node: `matrix-uniform-critical-cutoff-mass`.
-/

open Set Metric Filter MeasureTheory
open scoped Topology

namespace GlobalEmbedding.Paper

/-- For a compact continuous family with period-null fiber zero sets, the actual smooth
critical-region cutoff averages tend uniformly to zero.

Proof: the cutoff lies in [0,1] and decreases with n. At every nonzero fiber value it
is eventually zero; dominated convergence gives pointwise convergence of its actual
period integrals. Joint continuity gives continuity of each actual period integral.
Apply native Dini to upgrade pointwise to uniform convergence on the compact parameter
space. Source: `prop:matrix` proof, line293, expanded cutoff argument. -/
theorem uniform_critical_cutoff_mass
    {K : Type*} [MetricSpace K] [CompactSpace K]
    (H : K × ℝ → ℝ) (hH : Continuous H)
    (hnull : ∀ k, ∀ᵐ t ∂volume.restrict (Icc (0 : ℝ) 1), H (k, t) ≠ 0) :
    TendstoUniformly
      (fun n : ℕ ↦ fun k : K ↦ ∫ t in Icc (0 : ℝ) 1,
        1 - Real.smoothTransition ((n : ℝ) * H (k, t) ^ 2 - 1))
      (fun _ : K ↦ (0 : ℝ)) atTop := by
  let C (n : ℕ) (z : K × ℝ) := 1 - Real.smoothTransition ((n : ℝ) * H z ^ 2 - 1)
  have hC (n : ℕ) : Continuous (C n) := by dsimp only [C]; fun_prop
  have hs (n : ℕ) (k : K) : Continuous (fun t : ℝ ↦ C n (k, t)) :=
    (hC n).comp (continuous_const.prodMk continuous_id)
  have hnonneg (n : ℕ) (z : K × ℝ) : 0 ≤ C n z :=
    sub_nonneg.mpr (Real.smoothTransition.le_one _)
  have hone (n : ℕ) (z : K × ℝ) : C n z ≤ 1 := by
    exact sub_le_self _ (Real.smoothTransition.nonneg _)
  have hpoint (k : K) :
      Tendsto (fun n ↦ ∫ t in Icc (0 : ℝ) 1, C n (k, t)) atTop (𝓝 0) := by
    have h := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Icc (0 : ℝ) 1)) (F := fun n t ↦ C n (k, t))
      (f := fun _ ↦ (0 : ℝ)) (fun _ ↦ 1)
      (fun n ↦ (hs n k).aestronglyMeasurable)
      (integrableOn_const isCompact_Icc.measure_ne_top)
      (fun n ↦ .of_forall fun t ↦ by
        rw [Real.norm_eq_abs, abs_of_nonneg (hnonneg n (k, t))]
        exact hone n (k, t)) ?_
    · simpa only [integral_zero] using h
    · filter_upwards [hnull k] with t ht
      have hpos : 0 < H (k, t) ^ 2 := sq_pos_of_ne_zero ht
      obtain ⟨N, hN⟩ := exists_nat_gt (2 / H (k, t) ^ 2)
      have hzero : (fun n : ℕ ↦ C n (k, t)) =ᶠ[atTop] fun _ ↦ 0 := by
        filter_upwards [eventually_ge_atTop N] with n hn
        have hcast : (N : ℝ) ≤ n := by exact_mod_cast hn
        have htwo : 2 ≤ (n : ℝ) * H (k, t) ^ 2 :=
          le_trans (le_of_lt ((div_lt_iff₀ hpos).mp hN))
            (mul_le_mul_of_nonneg_right hcast hpos.le)
        simp only [C, Real.smoothTransition.one_of_one_le (by linarith :
          1 ≤ (n : ℝ) * H (k, t) ^ 2 - 1), sub_self]
      exact tendsto_const_nhds.congr' hzero.symm
  apply Antitone.tendstoUniformly_of_forall_tendsto
    (fun n ↦ continuous_parametric_integral_of_continuous (hC n) isCompact_Icc)
    ?_ continuous_const hpoint
  intro n m hnm k
  apply integral_mono (hs m k).continuousOn.integrableOn_Icc
    (hs n k).continuousOn.integrableOn_Icc
  intro t
  apply sub_le_sub_left
  apply Real.smoothTransition.monotone
  exact sub_le_sub_right (mul_le_mul_of_nonneg_right (by exact_mod_cast hnm)
    (sq_nonneg _)) 1

#print axioms uniform_critical_cutoff_mass

end GlobalEmbedding.Paper
