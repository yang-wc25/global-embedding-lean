import NormalPolar.Response
import NormalPolar.ConstructionNormalEquiv
import Mathlib.Analysis.Calculus.MeanValue

/-!
# A linear same-Q gap on every fixed genuine projection reserve

The explicit polar formula is differentiated on the convex intersection of
two operator balls. The same derivative constant already used by the actual
parameter response therefore controls the zeroth-order gap on the entire
original reserve q < 1. No smaller scale or parameter ball is selected.
-/

noncomputable section
open Set
open scoped ContDiff Topology

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- Fixing the old projection leaves the existing universal derivative
constant unchanged. The intermediate operators need not be projections. -/
theorem norm_fderiv_actualPolarOperator_right_le_reserve
    (q : ℝ) (hq : q < 1) (P R : V →L[ℝ] V)
    (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1) (hgap : ‖P - R‖ ≤ q) :
    ‖fderiv ℝ (fun T ↦ actualPolarOperator P T) R‖ ≤
      polarResponseConstantOn V q hq := by
  apply ContinuousLinearMap.opNorm_le_bound _ (polarResponseConstantOn_nonneg q hq)
  intro a
  simpa only [fderiv_fun_id, ContinuousLinearMap.id_apply] using
    norm_fderiv_actualPolarOperator_apply_le_reserve q hq P
      (fun T : V →L[ℝ] V ↦ T) R a differentiableAt_id hP hR hgap

/-- Linear control of the actual polar operator on an arbitrary fixed
reserve. The constant precedes both projections and all geometric data. -/
theorem norm_actualPolarOperator_sub_projection_le_reserve
    (q : ℝ) (hq : q < 1) (P R : V →L[ℝ] V)
    (hPP : P * P = P) (hP : ‖P‖ ≤ 1) (hR : ‖R‖ ≤ 1)
    (hgap : ‖P - R‖ ≤ q) :
    ‖actualPolarOperator P R - P‖ ≤
      polarResponseConstantOn V q hq * ‖P - R‖ := by
  let s : Set (V →L[ℝ] V) := Metric.closedBall 0 1 ∩ Metric.closedBall P q
  have hs : Convex ℝ s := (convex_closedBall (0 : V →L[ℝ] V) 1).inter
    (convex_closedBall P q)
  have hd (T : V →L[ℝ] V) (hT : T ∈ s) :
      DifferentiableAt ℝ (fun S ↦ actualPolarOperator P S) T := by
    have hclose : ‖P - T‖ < 1 := by
      have ht : ‖P - T‖ ≤ q := by
        simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hT.2
      exact ht.trans_lt hq
    exact ((contDiffAt_actualPolarPair (P, T) hclose).differentiableAt (by simp)).comp T
      (differentiableAt_const P |>.prodMk differentiableAt_id)
  have hb (T : V →L[ℝ] V) (hT : T ∈ s) :
      ‖fderiv ℝ (fun S ↦ actualPolarOperator P S) T‖ ≤
        polarResponseConstantOn V q hq := by
    exact norm_fderiv_actualPolarOperator_right_le_reserve q hq P T hP
      (by simpa only [Metric.mem_closedBall, dist_zero_right] using hT.1)
      (by simpa only [Metric.mem_closedBall, dist_eq_norm, norm_sub_rev] using hT.2)
  have hq0 : 0 ≤ q := (norm_nonneg (P - R)).trans hgap
  have hPs : P ∈ s := by
    exact ⟨by simpa using hP, by simpa using hq0⟩
  have hRs : R ∈ s := by
    exact ⟨by simpa using hR, by simpa [dist_eq_norm, norm_sub_rev] using hgap⟩
  have h := hs.norm_image_sub_le_of_norm_fderiv_le hd hb hPs hRs
  have hdiag : actualPolarOperator P P = P := by
    simp only [actualPolarOperator, sub_self, zero_pow (by decide : 2 ≠ 0),
      actualInvSqrt_zero, one_mul, hPP]
  simpa only [hdiag, norm_sub_rev] using h

/-- The same estimate for the true orthogonal projections of two actual
normal spaces, with no rank hypothesis and no preselected identification. -/
theorem norm_actualNormalPolarOperator_sub_projection_le_reserve
    (q : ℝ) (hq : q < 1) (K L : Submodule ℝ V)
    (hgap : ‖K.starProjection - L.starProjection‖ ≤ q) :
    ‖actualPolarOperator K.starProjection L.starProjection - K.starProjection‖ ≤
      polarResponseConstantOn V q hq * ‖K.starProjection - L.starProjection‖ := by
  apply norm_actualPolarOperator_sub_projection_le_reserve q hq K.starProjection L.starProjection
  · exact K.isIdempotentElem_starProjection
  · exact K.starProjection_norm_le
  · exact L.starProjection_norm_le
  · exact hgap

end GlobalEmbedding.NormalPolar
