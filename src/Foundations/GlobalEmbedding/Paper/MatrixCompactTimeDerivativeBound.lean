import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Order.Compact

/-!
# Actual joint time derivatives and their compact uniform bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line293.
DAG node: `matrix-compact-time-derivative-bound`.
-/

open Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- Actual joint smoothness gives actual joint smoothness of the time derivative.

Proof: evaluate the actual joint Frechet derivative on (0,1), a native smooth
bilinear evaluation. The actual chain rule for t↦(p,t) identifies this expression
with the actual one-variable derivative. Source: `prop:matrix` cutoff proof. -/
theorem contDiffOn_time_derivative
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U : Set P} (hU : IsOpen U) (F : P × ℝ → E)
    (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) :
    ContDiffOn ℝ ∞ (fun z : P × ℝ ↦ deriv (fun t ↦ F (z.1, t)) z.2)
      (U ×ˢ univ) := by
  have hopen : IsOpen (U ×ˢ (univ : Set ℝ)) := hU.prod isOpen_univ
  have hd : ContDiffOn ℝ ∞ (fun z ↦ (fderiv ℝ F z) (0, 1)) (U ×ˢ univ) :=
    (hF.fderiv_of_isOpen hopen (by simp)).clm_apply contDiffOn_const
  apply hd.congr
  intro z hz
  have hc := ((hF.contDiffAt (hopen.mem_nhds hz)).differentiableAt
    (by simp)).hasFDerivAt.comp z.2 (hasFDerivAt_prodMk_right (𝕜 := ℝ) z.1 z.2)
  exact hc.hasDerivAt.deriv

/-- The actual time derivatives of a jointly smooth family have a common bound
on every actual compact parameter set times every compact time interval.

Proof: use actual joint smoothness of the time derivative, restrict its actual
continuity to K×Icc a b, then native compact norm boundedness. This derives
the bound from original smooth compact data. Source: `prop:matrix`, line293. -/
theorem compact_time_derivative_bound
    {P E : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    [NormedAddCommGroup E] [NormedSpace ℝ E]
    {U K : Set P} (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (F : P × ℝ → E) (hF : ContDiffOn ℝ ∞ F (U ×ˢ univ)) (a b : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p ∈ K, ∀ t ∈ Icc a b,
      ‖deriv (fun s ↦ F (p, s)) t‖ ≤ C := by
  have hcont := (contDiffOn_time_derivative hU F hF).continuousOn
  obtain ⟨C, hC⟩ := (hK.prod isCompact_Icc).exists_bound_of_continuousOn
    (hcont.mono (Set.prod_mono hKU (subset_univ _)))
  refine ⟨max C 0, le_max_right _ _, ?_⟩
  intro p hp t ht
  exact (hC (p, t) ⟨hp, ht⟩).trans (le_max_left _ _)

#print axioms contDiffOn_time_derivative
#print axioms compact_time_derivative_bound

end GlobalEmbedding.Paper
