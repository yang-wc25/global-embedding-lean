import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Instances.Real.Lemmas

/-!
# Uniform coefficient and linear forcing bounds on genuine compact parameter sets

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 403–425.
DAG node: `balanced-compact-data-uniform-bounds`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Genuine compactness and C¹ forcing give uniform data bounds on one time interval.

Choose half the original time radius. The actual compact product with its closed real ball
bounds the continuous coefficient and the actual full forcing derivative. At each allowed
base point apply the genuine mean-value inequality only on the convex product of that
singleton with the time ball. Vanishing forcing at time zero gives the uniform linear bound.
No convexity of the compact base set, prior uniform bounds, or exterior data are assumed.
Source: uniform small forcing and coefficients on compact local parameter sets in the
contraction step of `lem:balanced`. -/
theorem balanced_compact_data_uniform_bounds
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) (hR : 0 < R) (A : E × ℝ → Y →L[ℝ] X) (f : E × ℝ → X)
    (hA : ContinuousOn A (U ×ˢ Metric.ball (0 : ℝ) R))
    (hf : ContDiffOn ℝ 1 f (U ×ˢ Metric.ball (0 : ℝ) R))
    (hf0 : ∀ p ∈ K, f (p, 0) = 0) :
    ∃ r L C : ℝ, 0 < r ∧ r < R ∧ 0 < L ∧ 0 < C ∧
      ∀ z ∈ K ×ˢ Metric.closedBall (0 : ℝ) r, ‖A z‖ ≤ L ∧ ‖f z‖ ≤ C * |z.2| := by
  let r := R / 2
  have hr : 0 < r := by dsimp [r]; positivity
  have hrR : r < R := by dsimp [r]; linarith
  have hsub : K ×ˢ Metric.closedBall (0 : ℝ) r ⊆ U ×ˢ Metric.ball (0 : ℝ) R := by
    intro z hz
    exact ⟨hKU hz.1, (Metric.mem_closedBall.mp hz.2).trans_lt hrR⟩
  have hcompact : IsCompact (K ×ˢ Metric.closedBall (0 : ℝ) r) :=
    hK.prod (isCompact_closedBall (0 : ℝ) r)
  obtain ⟨L₀, hL₀⟩ := hcompact.exists_bound_of_continuousOn (hA.mono hsub)
  have hdf := hf.continuousOn_fderiv_of_isOpen (hU.prod Metric.isOpen_ball) (by norm_num)
  obtain ⟨C₀, hC₀⟩ := hcompact.exists_bound_of_continuousOn (hdf.mono hsub)
  let L := |L₀| + 1
  let C := |C₀| + 1
  have hL : 0 < L := by dsimp [L]; positivity
  have hC : 0 < C := by dsimp [C]; positivity
  refine ⟨r, L, C, hr, hrR, hL, hC, ?_⟩
  intro z hz
  have hAb : ‖A z‖ ≤ L := (hL₀ z hz).trans
    ((le_abs_self L₀).trans (by dsimp [L]; linarith))
  refine ⟨hAb, ?_⟩
  let S := {z.1} ×ˢ Metric.closedBall (0 : ℝ) r
  have hSK : S ⊆ K ×ˢ Metric.closedBall (0 : ℝ) r := by
    intro y hy
    exact ⟨by simpa only [mem_singleton_iff.mp hy.1] using hz.1, hy.2⟩
  have hdiff : ∀ y ∈ S, DifferentiableAt ℝ f y := by
    intro y hy
    have hlocal := hf.contDiffAt ((hU.prod Metric.isOpen_ball).mem_nhds (hsub (hSK hy)))
    exact hlocal.differentiableAt (by norm_num)
  have hderiv : ∀ y ∈ S, ‖fderiv ℝ f y‖ ≤ C := by
    intro y hy
    exact (hC₀ y (hSK hy)).trans
      ((le_abs_self C₀).trans (by dsimp [C]; linarith))
  have hconvex : Convex ℝ S := (convex_singleton z.1).prod (convex_closedBall (0 : ℝ) r)
  have h0 : (z.1, (0 : ℝ)) ∈ S := ⟨rfl, by simpa using hr.le⟩
  have ht : z ∈ S := ⟨rfl, hz.2⟩
  have h := hconvex.norm_image_sub_le_of_norm_fderiv_le hdiff hderiv h0 ht
  rw [hf0 z.1 hz.1, sub_zero] at h
  simpa only [Prod.norm_def, Prod.fst_sub, Prod.snd_sub, sub_self, sub_zero, norm_zero,
    Real.norm_eq_abs, max_eq_right (abs_nonneg z.2)] using h

#print axioms balanced_compact_data_uniform_bounds

end GlobalEmbedding.Paper
