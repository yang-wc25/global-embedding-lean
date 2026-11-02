import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Actual finite curvature-zero sets of analytic closed unit-speed planar profiles

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines291–307.
DAG node: `matrix-analytic-planar-curvature-null`.
-/

open Set Filter MeasureTheory

namespace GlobalEmbedding.Paper

/-- For actual analytic closed unit-speed planar profiles the actual curvature
zero set is finite on each compact interval and the actual flat curvature weight
is strictly positive almost everywhere there.

Proof: actual κ=f′g″−g′f″ is analytic. If identically zero, differentiation of
actual unit speed gives ss′+tt′=0, and κ=0 gives st′−ts′=0. Actual s²+t²=1
forces s′=0. Native derivative constancy makes s constant. Native Rolle zeros
of s and t then contradict unit speed. The native analytic zero dichotomy and
compact codiscrete theorem make actual κ zeros finite. Finite sets have zero
actual volume; actual expNegInvGlue(κ²) is positive wherever κ≠0.
Source: `prop:matrix`, finite curvature-zero assertion in line307. -/
theorem analytic_planar_curvature_null
    (f g : ℝ → ℝ) (hf : AnalyticOnNhd ℝ f univ) (hg : AnalyticOnNhd ℝ g univ)
    (hfperiod : Function.Periodic f 1) (hgperiod : Function.Periodic g 1)
    (hunit : ∀ x, deriv f x ^ 2 + deriv g x ^ 2 = 1) (a b : ℝ) :
    let κ : ℝ → ℝ := fun x ↦ deriv f x * deriv (deriv g) x -
      deriv g x * deriv (deriv f) x
    {x : ℝ | x ∈ Icc a b ∧ κ x = 0}.Finite ∧
      ∀ᵐ x ∂volume.restrict (Icc a b), 0 < expNegInvGlue (κ x ^ 2) := by
  intro κ
  have hdf := hf.deriv
  have hdg := hg.deriv
  have hκ : AnalyticOnNhd ℝ κ univ := (hdf.mul hdg.deriv).sub (hdg.mul hdf.deriv)
  have hnot : ¬EqOn κ 0 univ := by
    intro hz
    have hsprime (x : ℝ) : deriv (deriv f) x = 0 := by
      have hd := (((hdf x (mem_univ x)).differentiableAt.hasDerivAt).pow 2).add
        (((hdg x (mem_univ x)).differentiableAt.hasDerivAt).pow 2)
      have heq : (fun y ↦ deriv f y ^ 2 + deriv g y ^ 2) = fun _ ↦ (1 : ℝ) := funext hunit
      have hzero : deriv (fun y ↦ deriv f y ^ 2 + deriv g y ^ 2) x = 0 := by rw [heq]; simp
      have hdval := hd.deriv
      change deriv (fun y ↦ deriv f y ^ 2 + deriv g y ^ 2) x = _ at hdval
      rw [hzero] at hdval
      norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one] at hdval
      have horth : deriv f x * deriv (deriv f) x + deriv g x * deriv (deriv g) x = 0 := by
        nlinarith
      have hdet : deriv f x * deriv (deriv g) x - deriv g x * deriv (deriv f) x = 0 :=
        hz (mem_univ x)
      have h1 := congrArg (fun r : ℝ ↦ r * deriv f x) horth
      have h2 := congrArg (fun r : ℝ ↦ r * deriv g x) hdet
      have hu := congrArg (fun r : ℝ ↦ deriv (deriv f) x * r) (hunit x)
      nlinarith
    have hsconstant := is_const_of_deriv_eq_zero
      (fun x ↦ (hdf x (mem_univ x)).differentiableAt) hsprime
    obtain ⟨xf, _, hxf⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
      (fun x _ ↦ (hf x (mem_univ x)).continuousAt.continuousWithinAt)
      (by simpa only [zero_add] using (hfperiod 0).symm)
    obtain ⟨xg, _, hxg⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
      (fun x _ ↦ (hg x (mem_univ x)).continuousAt.continuousWithinAt)
      (by simpa only [zero_add] using (hgperiod 0).symm)
    have hsxg : deriv f xg = 0 := (hsconstant xg xf).trans hxf
    have hu := hunit xg
    rw [hsxg, hxg] at hu
    norm_num at hu
  have hdisc := (hκ.eqOn_zero_or_eventually_ne_zero_of_preconnected
    isPreconnected_univ).resolve_left hnot
  have hfinite := isCompact_Icc.finite_sdiff_of_mem_codiscreteWithin
    ((Filter.codiscreteWithin_mono (subset_univ (Icc a b))) hdisc)
  have hzeros : {x : ℝ | x ∈ Icc a b ∧ κ x = 0}.Finite := by
    convert hfinite using 1
    ext x
    simp
  refine ⟨hzeros, ?_⟩
  have hnonzero : ∀ᵐ x ∂volume.restrict (Icc a b), κ x ≠ 0 := by
    rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
    simpa only [not_imp, ne_eq, not_not] using hzeros.measure_zero volume
  filter_upwards [hnonzero] with x hx
  exact expNegInvGlue.pos_of_pos (sq_pos_of_ne_zero hx)

#print axioms analytic_planar_curvature_null

end GlobalEmbedding.Paper
