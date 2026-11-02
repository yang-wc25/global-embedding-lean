import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateIntegral
import GlobalEmbedding.Paper.LittlePeriodicCAlphaDerivativeParameter
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateFiniteRank

/-!
# Actual Fréchet derivative at zero of a little Hölder translation orbit

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-translation-derivative-zero`.
-/

open Filter Set MeasureTheory intervalIntegral
open scoped Topology

namespace GlobalEmbedding.Paper

/-- The actual lower-space translation orbit has the actual direction-derivative parameter
map as its Fréchet derivative at zero, for high/low representatives of the same lift.

Proof: translated compositions of the finite-domain derivative map are operator-norm
continuous. For small h their difference from the zero-shift map is bounded by ε uniformly
on the segment t h, 0≤t≤1. The proved norm-level Bochner identity expresses the Fréchet
remainder as the integral of this operator difference applied to h; its norm is ≤ε‖h‖.
This proves the little-o criterion. Source: translation difference quotients in `lem:balanced`. -/
theorem littlePeriodicCAlpha_translate_hasFDerivAt_zero {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N (k + 1) α)
    (g : LittlePeriodicCAlphaFunction a N k α) (hfg : f.val.toFun = g.val.toFun)
    (hα : α ≤ 1) :
    HasFDerivAt (fun h : EuclideanSpace ℝ (Fin a) ↦ littlePeriodicCAlphaTranslateIsometry h g)
      (littlePeriodicCAlphaDerivativeParameter f) 0 := by
  let A := littlePeriodicCAlphaDerivativeParameter f
  let B (u : EuclideanSpace ℝ (Fin a)) :=
    (littlePeriodicCAlphaTranslateIsometry u).toContinuousLinearMap.comp A
  have hzero (q : LittlePeriodicCAlphaFunction a N k α) :
      littlePeriodicCAlphaTranslateIsometry 0 q = q := by
    apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    change q.val.toFun (x + 0) = q.val.toFun x
    simp
  have hB0 : B 0 = A := by
    apply ContinuousLinearMap.ext
    intro v
    exact hzero (A v)
  have hB : Continuous B := littlePeriodicCAlpha_translate_finite_rank_continuous A hα
  rw [hasFDerivAt_iff_isLittleO]
  simp only [hzero, sub_zero]
  apply Asymptotics.IsLittleO.of_bound
  intro ε hε
  obtain ⟨δ, hδ, hδbound⟩ :=
    (Metric.continuousAt_iff (f := B) (a := 0)).mp hB.continuousAt ε hε
  filter_upwards [Metric.ball_mem_nhds (0 : EuclideanSpace ℝ (Fin a)) hδ] with h hh
  have hh0 : ‖h‖ < δ := by simpa only [Metric.mem_ball, dist_zero_right] using hh
  have hpoint (t : ℝ) (ht : t ∈ uIoc (0 : ℝ) 1) :
      ‖(B (t • h) - A) h‖ ≤ ε * ‖h‖ := by
    have ht' : t ∈ Ioc (0 : ℝ) 1 := by simpa only [uIoc_of_le zero_le_one] using ht
    have hnorm : ‖t • h‖ ≤ ‖h‖ := by
      rw [norm_smul, Real.norm_of_nonneg ht'.1.le]
      exact (mul_le_mul_of_nonneg_right ht'.2 (norm_nonneg h)).trans_eq (one_mul _)
    have hsmall : dist (t • h) 0 < δ := by
      rw [dist_zero_right]
      exact hnorm.trans_lt hh0
    have hoperator : ‖B (t • h) - A‖ ≤ ε := by
      rw [← dist_eq_norm (B (t • h)) A]
      simpa only [hB0] using (hδbound hsmall).le
    exact ((B (t • h) - A).le_opNorm h).trans
      (mul_le_mul_of_nonneg_right hoperator (norm_nonneg _))
  have hF : Continuous (fun t : ℝ ↦ littlePeriodicCAlphaTranslateIsometry (t • h) (A h)) :=
    (littlePeriodicCAlpha_translate_joint_continuous hα).comp
      ((continuous_id.smul continuous_const).prodMk continuous_const)
  have hintegral : (∫ t : ℝ in 0..1, (B (t • h) - A) h) =
      littlePeriodicCAlphaTranslateIsometry h g - g - A h := by
    change (∫ t : ℝ in 0..1, littlePeriodicCAlphaTranslateIsometry (t • h) (A h) - A h) = _
    rw [intervalIntegral.integral_sub (hF.intervalIntegrable 0 1) intervalIntegrable_const]
    simp only [intervalIntegral.integral_const, sub_zero, one_smul]
    have hFTC : (∫ t : ℝ in 0..1, littlePeriodicCAlphaTranslateIsometry (t • h) (A h)) =
        littlePeriodicCAlphaTranslateIsometry h g - g :=
      littlePeriodicCAlpha_translate_integral f g hfg hα h
    exact congrArg (fun q ↦ q - A h) hFTC
  change ‖littlePeriodicCAlphaTranslateIsometry h g - g - A h‖ ≤ ε * ‖h‖
  rw [← hintegral]
  simpa only [sub_zero, abs_one, mul_one] using
    intervalIntegral.norm_integral_le_of_norm_le_const hpoint

#print axioms littlePeriodicCAlpha_translate_hasFDerivAt_zero

end GlobalEmbedding.Paper
