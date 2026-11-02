import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual finite critical sets for nonconstant analytic orbit profiles

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof, line293.
DAG node: `matrix-analytic-finite-critical-set`.
-/

open Set Filter MeasureTheory

namespace GlobalEmbedding.Paper

/-- An actual nonconstant real analytic function has finitely many actual critical points
on every compact interval, and its actual derivative is nonzero almost everywhere there.

Proof: its actual derivative is analytic. If identically zero, native mean value
constancy contradicts the two distinct function values. The analytic zero dichotomy
therefore makes the derivative nonzero off a codiscrete set. Restrict codiscreteness to
the compact interval; native compact-codiscrete finiteness gives the finite critical set.
Finite sets have zero actual volume, proving the restricted almost-everywhere statement.
Source: `prop:matrix` proof, line293. -/
theorem analytic_finite_critical_set
    (f : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f univ)
    (hnonconstant : ∃ x y, f x ≠ f y) (a b : ℝ) :
    {t : ℝ | t ∈ Icc a b ∧ deriv f t = 0}.Finite ∧
      ∀ᵐ t ∂volume.restrict (Icc a b), deriv f t ≠ 0 := by
  have hnot : ¬EqOn (deriv f) 0 univ := by
    intro hz
    obtain ⟨x, y, hxy⟩ := hnonconstant
    apply hxy
    exact is_const_of_deriv_eq_zero (fun t ↦ (hf t (mem_univ t)).differentiableAt)
      (fun t ↦ hz (mem_univ t)) x y
  have hdisc := (hf.deriv.eqOn_zero_or_eventually_ne_zero_of_preconnected
    isPreconnected_univ).resolve_left hnot
  have hfinite := isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin
    ((Filter.codiscreteWithin_mono (subset_univ (Icc a b))) hdisc)
  have hcritical : {t : ℝ | t ∈ Icc a b ∧ deriv f t = 0}.Finite := by
    convert hfinite using 1
    ext t
    simp
  refine ⟨hcritical, ?_⟩
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
  simpa only [not_imp, ne_eq, not_not] using hcritical.measure_zero volume

#print axioms analytic_finite_critical_set

end GlobalEmbedding.Paper
