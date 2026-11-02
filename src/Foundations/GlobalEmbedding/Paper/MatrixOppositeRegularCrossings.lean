import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.ContDiff.RCLike
import Mathlib.Analysis.Calculus.ContDiff.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
import Mathlib.Topology.DiscreteSubset

/-!
# Genuine opposite regular crossings for periodic real functions

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines327–332.
DAG node: `cone-opposite-regular-crossings`.
-/
noncomputable section
open Set Filter Metric MeasureTheory
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- A genuine periodic differentiable monotone function has zero derivative everywhere. -/
private theorem periodic_nonnegative_derivative_zero
    (g g' : ℝ → ℝ) (hp : Function.Periodic g 1)
    (hd : ∀ x, HasDerivAt g (g' x) x) (hn : ∀ x, 0 ≤ g' x) (a : ℝ) : g' a = 0 := by
  have hm : Monotone g := monotone_of_hasDerivAt_nonneg hd hn
  have hmax : IsLocalMax g a := by
    filter_upwards [Iio_mem_nhds (show a < a + 1 by linarith)] with x hx
    exact (hm hx.le).trans_eq (hp a)
  exact hmax.hasDerivAt_eq_zero (hd a)

/-- A nonconstant actual differentiable periodic real function has a positive derivative. -/
private theorem periodic_exists_positive_derivative
    (f : ℝ → ℝ) (hp : Function.Periodic f 1) (hd : Differentiable ℝ f)
    (hnc : ∃ x y, f x ≠ f y) : ∃ a, 0 < deriv f a := by
  by_contra hbad
  push Not at hbad
  have hz (a : ℝ) : deriv f a = 0 := by
    have hh := periodic_nonnegative_derivative_zero (fun x ↦ -f x) (fun x ↦ -deriv f x)
      (fun x ↦ by simp only [hp x]) (fun x ↦ (hd x).hasDerivAt.neg)
      (fun x ↦ neg_nonneg.mpr (hbad x)) a
    exact neg_eq_zero.mp hh
  obtain ⟨x, y, hxy⟩ := hnc
  exact hxy (is_const_of_deriv_eq_zero hd hz x y)

/-- Every value interval containing a positive crossing contains an actual negative
crossing as well. A true smooth cutoff primitive rules out one-way passage. -/
private theorem periodic_negative_crossing_in_interval
    (f : ℝ → ℝ) (hp : Function.Periodic f 1) (hd : Differentiable ℝ f)
    (a l u : ℝ) (ha : 0 < deriv f a) (hl : l < f a) (hu : f a < u) :
    ∃ b, f b ∈ Ioo l u ∧ deriv f b < 0 := by
  by_contra hbad
  push Not at hbad
  let χ : ℝ → ℝ := fun x ↦ expNegInvGlue ((x - l) * (u - x))
  have hχ : Continuous χ :=
    (expNegInvGlue.contDiff : ContDiff ℝ ∞ expNegInvGlue).continuous.comp
      ((continuous_id.sub continuous_const).mul (continuous_const.sub continuous_id))
  have hχn (x : ℝ) : 0 ≤ χ x := expNegInvGlue.nonneg _
  have hχmem (x : ℝ) (hx : χ x ≠ 0) : x ∈ Ioo l u := by
    have hh : 0 < (x - l) * (u - x) := by
      apply lt_of_not_ge
      exact fun he ↦ hx (expNegInvGlue.zero_of_nonpos he)
    rcases mul_pos_iff.mp hh with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · exact ⟨by linarith, by linarith⟩
    · have hlu : l < u := hl.trans hu
      exfalso
      linarith
  let Φ : ℝ → ℝ := fun x ↦ ∫ t in (0 : ℝ)..x, χ t
  have hΦ (x : ℝ) : HasDerivAt Φ (χ x) x :=
    intervalIntegral.integral_hasDerivAt_right (hχ.intervalIntegrable _ _)
      hχ.aestronglyMeasurable.stronglyMeasurableAtFilter hχ.continuousAt
  have hcomp (x : ℝ) : HasDerivAt (fun t ↦ Φ (f t)) (χ (f x) * deriv f x) x :=
    (hΦ (f x)).comp x (hd x).hasDerivAt
  have hnonneg (x : ℝ) : 0 ≤ χ (f x) * deriv f x := by
    by_cases hx : χ (f x) = 0
    · simp [hx]
    · exact mul_nonneg (hχn _) (hbad x (hχmem _ hx))
  have hh := periodic_nonnegative_derivative_zero (fun t ↦ Φ (f t))
    (fun t ↦ χ (f t) * deriv f t) (fun t ↦ congrArg Φ (hp t)) hcomp hnonneg a
  have hχpos : 0 < χ (f a) := expNegInvGlue.pos_of_pos (mul_pos (sub_pos.mpr hl) (sub_pos.mpr hu))
  exact (mul_pos hχpos ha).ne' hh

/-- The actual inverse function theorem makes every source neighborhood of a genuine
regular point cover a neighborhood of its value. -/
private theorem regular_value_image_nhds
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (a : ℝ) (ha : deriv f a ≠ 0)
    {U : Set ℝ} (hU : U ∈ 𝓝 a) : f '' U ∈ 𝓝 (f a) := by
  rw [← (hf.hasStrictDerivAt one_ne_zero (x := a)).map_nhds_eq ha]
  change f ⁻¹' (f '' U) ∈ 𝓝 a
  exact mem_of_superset hU (fun x hx ↦ show f x ∈ f '' U from ⟨x, hx, rfl⟩)

/-- Every nonconstant actual C1 period-one function has a genuine nonempty open
interval of values each admitting two actual regular crossings of opposite sign.
No global circle lift, regular-value axiom, or given inverse branches are assumed. -/
theorem matrix_periodic_opposite_regular_crossings
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f 1)
    (hnc : ∃ x y, f x ≠ f y) :
    ∃ l u : ℝ, l < u ∧ ∀ y ∈ Ioo l u, ∃ a b : ℝ,
      f a = y ∧ f b = y ∧ 0 < deriv f a ∧ deriv f b < 0 := by
  have hd : Differentiable ℝ f := hf.differentiable one_ne_zero
  obtain ⟨a, ha⟩ := periodic_exists_positive_derivative f hp hd hnc
  let U : Set ℝ := {x | 0 < deriv f x}
  have hU : U ∈ 𝓝 a := hf.continuous_deriv_one.continuousAt (Ioi_mem_nhds ha)
  obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp (regular_value_image_nhds f hf a ha.ne' hU)
  obtain ⟨b, hb, hbneg⟩ := periodic_negative_crossing_in_interval f hp hd a
    (f a - δ / 2) (f a + δ / 2) ha (by linarith) (by linarith)
  have hbball : f b ∈ ball (f a) δ := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hb.1, hb.2]
  let V : Set ℝ := {x | deriv f x < 0}
  have hV : V ∈ 𝓝 b := hf.continuous_deriv_one.continuousAt (Iio_mem_nhds hbneg)
  have hW : ball (f a) δ ∩ f '' V ∈ 𝓝 (f b) :=
    inter_mem (isOpen_ball.mem_nhds hbball) (regular_value_image_nhds f hf b hbneg.ne hV)
  obtain ⟨ε, hε, hεball⟩ := Metric.mem_nhds_iff.mp hW
  refine ⟨f b - ε, f b + ε, by linarith, ?_⟩
  intro y hy
  have hyball : y ∈ ball (f b) ε := by
    rw [mem_ball, Real.dist_eq, abs_lt]
    constructor <;> linarith [hy.1, hy.2]
  obtain ⟨hyp, hyn⟩ := hεball hyball
  obtain ⟨p, hpU, hpy⟩ := hball hyp
  obtain ⟨n, hnV, hny⟩ := hyn
  exact ⟨p, n, hpy, hny, hpU, hnV⟩

/-- A genuine nonempty real interval contains a smaller nonempty interval avoiding
any prescribed discrete set, including discrete sets that are not closed. -/
private theorem interval_avoiding_discrete (l u : ℝ) (hlu : l < u)
    (D : Set ℝ) (hD : IsDiscrete D) :
    ∃ l' u' : ℝ, l' < u' ∧ Ioo l' u' ⊆ Ioo l u ∧ Disjoint (Ioo l' u') D := by
  by_cases hn : (Ioo l u ∩ D).Nonempty
  · obtain ⟨x, hxI, hxD⟩ := hn
    obtain ⟨O, hO, hOD⟩ := isDiscrete_iff_forall_mem_exists_isOpen.mp hD x hxD
    have hxO : x ∈ O := by
      have hh : x ∈ O ∩ D := by rw [hOD]; exact mem_singleton x
      exact hh.1
    obtain ⟨δ, hδ, hball⟩ := Metric.mem_nhds_iff.mp
      ((hO.inter isOpen_Ioo).mem_nhds ⟨hxO, hxI⟩)
    refine ⟨x + δ / 4, x + δ / 2, by linarith, ?_, ?_⟩
    · intro y hy
      apply (hball ?_).2
      rw [mem_ball, Real.dist_eq, abs_lt]
      constructor <;> linarith [hy.1, hy.2]
    · apply Set.disjoint_left.mpr
      intro y hy hyD
      have hyO : y ∈ O := by
        apply (hball ?_).1
        rw [mem_ball, Real.dist_eq, abs_lt]
        constructor <;> linarith [hy.1, hy.2]
      have hyx : y = x := by
        have hh : y ∈ O ∩ D := ⟨hyO, hyD⟩
        rwa [hOD, mem_singleton_iff] at hh
      linarith [hy.1]
  · refine ⟨l, u, hlu, Subset.rfl, ?_⟩
    exact Set.disjoint_left.mpr (fun y hy hyD ↦ hn ⟨y, hy, hyD⟩)

/-- The true regular opposite-crossing interval can avoid any prescribed discrete
set of values. This gives the full source crossing statement in the stronger C1 form. -/
theorem matrix_periodic_opposite_regular_crossings_avoiding
    (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (hp : Function.Periodic f 1)
    (hnc : ∃ x y, f x ≠ f y) (D : Set ℝ) (hD : IsDiscrete D) :
    ∃ l u : ℝ, l < u ∧ Disjoint (Ioo l u) D ∧ ∀ y ∈ Ioo l u, ∃ a b : ℝ,
      f a = y ∧ f b = y ∧ 0 < deriv f a ∧ deriv f b < 0 := by
  obtain ⟨l, u, hlu, hc⟩ := matrix_periodic_opposite_regular_crossings f hf hp hnc
  obtain ⟨l', u', hlu', hsub, hd⟩ := interval_avoiding_discrete l u hlu D hD
  exact ⟨l', u', hlu', hd, fun y hy ↦ hc y (hsub hy)⟩

end GlobalEmbedding.Paper
