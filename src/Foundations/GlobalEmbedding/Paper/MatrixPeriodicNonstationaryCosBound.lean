import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

/-!
# Actual periodic nonlinear-phase integration by parts away from critical points

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, line293.
DAG node: `matrix-periodic-nonstationary-cos-bound`.
-/

open Set Filter MeasureTheory
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- An actual smooth periodic amplitude supported away from actual phase critical points
has an explicit inverse-frequency bound for its actual nonlinear-phase cosine average.

Proof: g=b/f' is genuinely smooth: use native division where f'≠0; where f'=0 the actual
support hypothesis makes b identically0 nearby, so g is the smooth zero function there.
Translation of derivatives makes g periodic. The actual derivative of sin(Tf+phase)/T
is f'cos(Tf+phase). Native integration by parts cancels the periodic endpoint term.
The remaining integral is bounded by the integral of |g'|/T using |sin|≤1.
Source: `prop:matrix` proof, line293. -/
theorem periodic_nonstationary_cos_bound
    (f b : ℝ → ℝ) (hf : ContDiff ℝ ∞ f) (hb : ContDiff ℝ ∞ b)
    (hfperiod : Function.Periodic f 1) (hbperiod : Function.Periodic b 1)
    (haway : ∀ x, deriv f x = 0 → x ∉ tsupport b)
    (T : ℝ) (hT : 0 < T) (phase : ℝ) :
    |∫ x in Icc (0 : ℝ) 1, b x * Real.cos (T * f x + phase)| ≤
      (∫ x in Icc (0 : ℝ) 1, |deriv (fun y ↦ b y / deriv f y) x|) / T := by
  let g : ℝ → ℝ := fun x ↦ b x / deriv f x
  have hdf : ContDiff ℝ ∞ (deriv f) := (contDiff_infty_iff_deriv.mp hf).2
  have hg : ContDiff ℝ ∞ g := by
    rw [contDiff_iff_contDiffAt]
    intro x
    by_cases hx : deriv f x = 0
    · have hz : g =ᶠ[𝓝 x] fun _ ↦ 0 := by
        filter_upwards [notMem_tsupport_iff_eventuallyEq.mp (haway x hx)] with y hy
        simp only [g, hy, Pi.zero_apply, zero_div]
      exact contDiffAt_const.congr_of_eventuallyEq hz
    · exact hb.contDiffAt.div hdf.contDiffAt hx
  have hdperiod : Function.Periodic (deriv f) 1 := by
    intro x
    rw [← deriv_comp_add_const]
    exact congrArg (fun u : ℝ → ℝ ↦ deriv u x) (funext hfperiod)
  have hgperiod : Function.Periodic g 1 := by
    intro x
    simp only [g, hbperiod x, hdperiod x]
  have hmul (x : ℝ) : g x * deriv f x = b x := by
    by_cases hx : deriv f x = 0
    · have hbzero : b x = 0 :=
        (notMem_tsupport_iff_eventuallyEq.mp (haway x hx)).self_of_nhds
      simp only [g, hx, hbzero, zero_div, mul_zero]
    · exact div_mul_cancel₀ (b x) hx
  let v : ℝ → ℝ := fun x ↦ Real.sin (T * f x + phase) / T
  have hv : ContDiff ℝ ∞ v := by dsimp only [v]; fun_prop
  have hvderiv (x : ℝ) :
      HasDerivAt v (deriv f x * Real.cos (T * f x + phase)) x := by
    have h := ((Real.hasDerivAt_sin (T * f x + phase)).comp x
      ((((hf.differentiable (by simp)) x).hasDerivAt.const_mul T).add_const phase)).div_const T
    convert h using 1
    · rfl
    · field_simp [hT.ne']
  have hgp : Continuous (deriv g) := (contDiff_infty_iff_deriv.mp hg).2.continuous
  have hvp : Continuous (fun x ↦ deriv f x * Real.cos (T * f x + phase)) := by fun_prop
  have hi := intervalIntegral.integral_mul_deriv_eq_deriv_mul_of_hasDerivAt
    (a := (0 : ℝ)) (b := 1) hg.continuous.continuousOn hv.continuous.continuousOn
    (fun x _ ↦ ((hg.differentiable (by simp)) x).hasDerivAt)
    (fun x _ ↦ hvderiv x) (hgp.intervalIntegrable 0 1) (hvp.intervalIntegrable 0 1)
  have hgend : g 1 = g 0 := by simpa only [zero_add] using hgperiod 0
  have hfend : f 1 = f 0 := by simpa only [zero_add] using hfperiod 0
  have hvend : v 1 = v 0 := by simp only [v, hfend]
  simp only [hgend, hvend, sub_self, zero_sub] at hi
  have hleft : (fun x ↦ g x * (deriv f x * Real.cos (T * f x + phase))) =
      (fun x ↦ b x * Real.cos (T * f x + phase)) := by
    funext x
    rw [← mul_assoc, hmul]
  have hright : (fun x ↦ deriv g x * v x) =
      (fun x ↦ (deriv g x * Real.sin (T * f x + phase)) / T) := by
    funext x
    dsimp only [v]
    ring
  rw [hleft, hright, intervalIntegral.integral_div] at hi
  have hbound : |∫ x in (0 : ℝ)..1, deriv g x * Real.sin (T * f x + phase)| ≤
      ∫ x in (0 : ℝ)..1, |deriv g x| := by
    have h := intervalIntegral.norm_integral_le_of_norm_le (show (0 : ℝ) ≤ 1 by norm_num)
      (μ := volume) (f := fun x ↦ deriv g x * Real.sin (T * f x + phase))
      (Filter.Eventually.of_forall fun x _ ↦ ?_) (hgp.abs.intervalIntegrable 0 1)
    · simpa only [Real.norm_eq_abs] using h
    · rw [Real.norm_eq_abs, abs_mul]
      exact (mul_le_mul_of_nonneg_left (Real.abs_sin_le_one _) (abs_nonneg _)).trans_eq
        (mul_one _)
  rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num),
    ← intervalIntegral.integral_of_le (show (0 : ℝ) ≤ 1 by norm_num)]
  change |∫ x in (0 : ℝ)..1, b x * Real.cos (T * f x + phase)| ≤
    (∫ x in (0 : ℝ)..1, |deriv g x|) / T
  rw [hi, abs_neg, abs_div, abs_of_pos hT]
  exact div_le_div_of_nonneg_right hbound hT.le

#print axioms periodic_nonstationary_cos_bound

end GlobalEmbedding.Paper
