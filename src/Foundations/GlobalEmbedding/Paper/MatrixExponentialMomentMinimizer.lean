import GlobalEmbedding.Paper.FinitePositiveSpanStability
import GlobalEmbedding.Paper.MatrixExponentialMomentCalculus
import Mathlib.Analysis.Calculus.LocalExtr.Basic
import Mathlib.Analysis.InnerProductSpace.LinearMap
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Convex.SpecificFunctions.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Tactic.Linarith

/-!
# The genuine coercive finite exponential moment minimizer

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`, lines345–350.
Positive spanning gives a genuine compact-sphere margin and an actual coercive minimum.
-/

noncomputable section
open Set Filter
open scoped Topology RealInnerProductSpace BigOperators

namespace GlobalEmbedding.Paper

variable {ι E : Type*} [Fintype ι] [Nonempty ι]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]

/-- Actual finite positive spanning has a uniform positive directional margin.
The index set is nonempty because the eventual density family includes h0=1;
zero-dimensional moment space is covered without a nontriviality assumption. -/
theorem matrix_positive_span_margin (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) :
    ∃ c : ℝ, 0 < c ∧ ∀ u : E, ∃ i, c * ‖u‖ ≤ ⟪v i, u⟫ := by
  classical
  obtain ⟨c, hc, hv⟩ := finite_positive_support_margin v (by
    simpa only [real_inner_comm] using hspan)
  refine ⟨c, hc, ?_⟩
  intro u
  by_cases hu : u = 0
  · subst u
    exact ⟨Classical.choice inferInstance, by simp⟩
  have hnorm : ‖‖u‖⁻¹ • u‖ = 1 := by
    rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.mpr (norm_nonneg _)),
      inv_mul_cancel₀ (norm_ne_zero_iff.mpr hu)]
  obtain ⟨i, hi⟩ := hv (‖u‖⁻¹ • u) hnorm
  refine ⟨i, ?_⟩
  rw [real_inner_comm, real_inner_smul_right] at hi
  have hh := mul_le_mul_of_nonneg_left hi (norm_nonneg u)
  rw [← mul_assoc, mul_inv_cancel₀ (norm_ne_zero_iff.mpr hu), one_mul] at hh
  simpa only [mul_comm] using hh

/-- The literal exponential potential dominates every prescribed level outside a genuine ball. -/
theorem matrix_finite_exponential_coercive (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (y : E) (K : ℝ) :
    ∃ R : ℝ, ∀ x : E, R ≤ ‖x‖ → K ≤ matrixExponentialPotential v y x := by
  classical
  obtain ⟨c, hc, hv⟩ := matrix_positive_span_margin v hspan
  have hquad (x : E) : c ^ 2 * ‖x‖ ^ 2 / 2 - ‖y‖ * ‖x‖ ≤
      matrixExponentialPotential v y x := by
    obtain ⟨i, hi⟩ := hv x
    have hbase : c ^ 2 * ‖x‖ ^ 2 / 2 ≤ ∑ j, Real.exp ⟪v j, x⟫ := by
      calc
        _ = (c * ‖x‖) ^ 2 / 2 := by ring
        _ ≤ Real.exp (c * ‖x‖) := by
          have hh := Real.quadratic_le_exp_of_nonneg (mul_nonneg hc.le (norm_nonneg x))
          nlinarith [mul_nonneg hc.le (norm_nonneg x)]
        _ ≤ Real.exp ⟪v i, x⟫ := Real.exp_le_exp.mpr hi
        _ ≤ _ := Finset.single_le_sum (f := fun j ↦ Real.exp ⟪v j, x⟫)
          (fun j _ ↦ (Real.exp_pos _).le) (Finset.mem_univ i)
    exact sub_le_sub hbase (real_inner_le_norm y x)
  refine ⟨max 1 (2 * (‖y‖ + |K| + 1) / c ^ 2), ?_⟩
  intro x hx
  have hx1 : 1 ≤ ‖x‖ := (le_max_left _ _).trans hx
  have hx2 : 2 * (‖y‖ + |K| + 1) ≤ ‖x‖ * c ^ 2 :=
    (div_le_iff₀ (sq_pos_of_pos hc)).mp ((le_max_right _ _).trans hx)
  have hmul := mul_le_mul_of_nonneg_right hx2 (norm_nonneg x)
  have hK := mul_le_mul_of_nonneg_left hx1 (abs_nonneg K)
  have hh := hquad x
  nlinarith [le_abs_self K, norm_nonneg x]

/-- Compact extrema yield an actual minimizer of the literal potential, with no supplied solver. -/
theorem matrix_finite_exponential_minimum (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (y : E) :
    ∃ x : E, ∀ z : E, matrixExponentialPotential v y x ≤
      matrixExponentialPotential v y z := by
  have hΦ : Continuous (matrixExponentialPotential v y) := by
    apply Continuous.sub
    · exact continuous_finsetSum _ (fun i _ ↦ (innerSL ℝ (v i)).continuous.rexp)
    · exact (innerSL ℝ y).continuous
  obtain ⟨R, hR⟩ := matrix_finite_exponential_coercive v hspan y
    (matrixExponentialPotential v y 0)
  apply hΦ.exists_forall_le' (0 : E)
  apply eventually_of_mem (isCompact_closedBall (0 : E) R).compl_mem_cocompact
  intro x hx
  apply hR x
  have hh : R < ‖x‖ := by
    simpa only [Set.mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le] using hx
  exact hh.le

/-- At the genuine minimum, Fermat's theorem solves the actual finite exponential moment equation. -/
theorem matrixExponentialMoment_surjective (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) :
    Function.Surjective (matrixExponentialMoment v) := by
  intro y
  obtain ⟨x, hx⟩ := matrix_finite_exponential_minimum v hspan y
  have hm : IsLocalMin (matrixExponentialPotential v y) x :=
    Filter.Eventually.of_forall hx
  have hz := hm.hasFDerivAt_eq_zero (matrixExponentialPotential_hasFDerivAt v y x)
  have he := congrArg (fun f : E →L[ℝ] ℝ ↦ f (matrixExponentialMoment v x - y)) hz
  have hzero : matrixExponentialMoment v x - y = 0 := by
    apply (inner_self_eq_zero (𝕜 := ℝ)).mp
    simpa only [innerSL_apply_apply, zero_apply] using he
  exact ⟨x, sub_eq_zero.mp hzero⟩

omit [Nonempty ι] [FiniteDimensional ℝ E] in
/-- Every genuine nontrivial segment has a strict exponential Jensen term. -/
theorem matrixExponentialPotential_strictConvex (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (y : E) :
    StrictConvexOn ℝ univ (matrixExponentialPotential v y) := by
  classical
  refine ⟨convex_univ, ?_⟩
  intro x _ z _ hxz a b ha hb hab
  obtain ⟨i, hi⟩ := hspan (x - z) (sub_ne_zero.mpr hxz)
  have hne : ⟪v i, x⟫ ≠ ⟪v i, z⟫ := by
    rw [inner_sub_right] at hi
    exact ne_of_gt (sub_pos.mp hi)
  have hle (j : ι) : Real.exp ⟪v j, a • x + b • z⟫ ≤
      a * Real.exp ⟪v j, x⟫ + b * Real.exp ⟪v j, z⟫ := by
    simpa only [inner_add_right, real_inner_smul_right, smul_eq_mul] using
      convexOn_exp.2 (mem_univ ⟪v j, x⟫) (mem_univ ⟪v j, z⟫) ha.le hb.le hab
  have hlt : Real.exp ⟪v i, a • x + b • z⟫ <
      a * Real.exp ⟪v i, x⟫ + b * Real.exp ⟪v i, z⟫ := by
    simpa only [inner_add_right, real_inner_smul_right, smul_eq_mul] using
      strictConvexOn_exp.2 (mem_univ ⟪v i, x⟫) (mem_univ ⟪v i, z⟫) hne ha hb hab
  have hs := Finset.sum_lt_sum (fun j (_ : j ∈ Finset.univ) ↦ hle j)
    ⟨i, Finset.mem_univ i, hlt⟩
  simp only [Finset.sum_add_distrib, ← Finset.mul_sum] at hs
  dsimp only [matrixExponentialPotential]
  simp only [inner_add_right, real_inner_smul_right, smul_eq_mul] at hs ⊢
  nlinarith

/-- The actual finite moment equation has exactly one solution for each prescribed vector. -/
theorem matrixExponentialMoment_existsUnique (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (y : E) :
    ∃! x : E, matrixExponentialMoment v x = y := by
  obtain ⟨x, hx⟩ := matrixExponentialMoment_surjective v hspan y
  exact ⟨x, hx, fun z hz ↦ matrixExponentialMoment_injective v hspan (hz.trans hx.symm)⟩

/-- The genuine strictly convex potential has exactly one actual global minimizer. -/
theorem matrixExponentialPotential_existsUnique_minimizer (v : ι → E)
    (hspan : ∀ u : E, u ≠ 0 → ∃ i, 0 < ⟪v i, u⟫) (y : E) :
    ∃! x : E, ∀ z : E, matrixExponentialPotential v y x ≤
      matrixExponentialPotential v y z := by
  obtain ⟨x, hx⟩ := matrix_finite_exponential_minimum v hspan y
  refine ⟨x, hx, ?_⟩
  intro z hz
  by_contra hzx
  have hh := (matrixExponentialPotential_strictConvex v hspan y).2
    (mem_univ z) (mem_univ x) hzx (show (0 : ℝ) < 1 / 2 by norm_num)
    (show (0 : ℝ) < 1 / 2 by norm_num) (show (1 : ℝ) / 2 + 1 / 2 = 1 by norm_num)
  have h1 := hx ((1 / 2 : ℝ) • z + (1 / 2 : ℝ) • x)
  have h2 := hz x
  simp only [smul_eq_mul] at hh
  linarith

#print axioms matrixExponentialPotential_existsUnique_minimizer
#print axioms matrixExponentialPotential_strictConvex
#print axioms matrix_finite_exponential_coercive
#print axioms matrix_finite_exponential_minimum
#print axioms matrixExponentialMoment_surjective
#print axioms matrixExponentialMoment_existsUnique

end GlobalEmbedding.Paper
