import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# Actual smooth quotient for the critical-region cutoff

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line293.
DAG node: `matrix-smooth-critical-cutoff-quotient`.
-/

open Set Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- The actual cutoff amplitude vanishes near every critical point, so its actual
quotient by the critical signal is smooth, even at zeros of that signal.

Proof: when H(x)=0, continuity makes nH²<1 on a neighborhood, where the actual
smoothTransition(nH²−1) is zero. Both actual amplitude and totalized quotient
are zero there. Elsewhere native smooth division applies. Multiplication back
by H equals the amplitude also at zeros. Source: `prop:matrix` cutoff proof. -/
theorem smooth_critical_cutoff_quotient
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    {U : Set P} (hU : IsOpen U) (H a : P → ℝ)
    (hH : ContDiffOn ℝ ∞ H U) (ha : ContDiffOn ℝ ∞ a U) (n : ℕ) :
    let B : P → ℝ := fun x ↦ a x * Real.smoothTransition ((n : ℝ) * H x ^ 2 - 1)
    ContDiffOn ℝ ∞ B U ∧
      ContDiffOn ℝ ∞ (fun x ↦ B x / H x) U ∧
      (∀ x ∈ U, H x = 0 → x ∉ tsupport B) ∧
      (∀ x, (B x / H x) * H x = B x) := by
  intro B
  have hB : ContDiffOn ℝ ∞ B U :=
    ha.mul (Real.smoothTransition.contDiff.comp_contDiffOn
      ((contDiffOn_const.mul (hH.pow 2)).sub contDiffOn_const))
  have hzero (x : P) (hx : x ∈ U) (hHx : H x = 0) :
      B =ᶠ[𝓝 x] fun _ ↦ 0 := by
    have hc : ContinuousAt (fun y ↦ (n : ℝ) * H y ^ 2) x :=
      continuousAt_const.mul ((hH.contDiffAt (hU.mem_nhds hx)).continuousAt.pow 2)
    have hsmall : ∀ᶠ y in 𝓝 x, (n : ℝ) * H y ^ 2 < 1 :=
      hc.eventually (gt_mem_nhds (by simp [hHx]))
    filter_upwards [hsmall] with y hy
    simp only [B, Real.smoothTransition.zero_of_nonpos (sub_nonpos.mpr hy.le), mul_zero]
  refine ⟨hB, ?_, ?_, ?_⟩
  · intro x hx
    apply ContDiffAt.contDiffWithinAt
    by_cases hHx : H x = 0
    · have hquot : (fun y ↦ B y / H y) =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [hzero x hx hHx] with y hy
        simp only [hy, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq hquot
    · exact (hB.contDiffAt (hU.mem_nhds hx)).div
        (hH.contDiffAt (hU.mem_nhds hx)) hHx
  · intro x hx hHx
    exact notMem_tsupport_iff_eventuallyEq.mpr (hzero x hx hHx)
  · intro x
    by_cases hHx : H x = 0
    · simp [B, hHx, Real.smoothTransition.zero_of_nonpos (show (-1 : ℝ) ≤ 0 by norm_num)]
    · exact div_mul_cancel₀ (B x) hHx

#print axioms smooth_critical_cutoff_quotient

end GlobalEmbedding.Paper
