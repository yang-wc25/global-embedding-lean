import GlobalEmbedding.Paper.BalancedUniformJointSmoothBranch
import GlobalEmbedding.Paper.BalancedCompactDataUniformBounds
import Mathlib.Topology.Separation.Regular

/-!
# A common actual smooth branch around every compact auxiliary parameter set

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 403–425.
DAG node: `balanced-compact-neighborhood-smooth-branch`.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Smooth data vanishing at zero construct one uniformly small branch near a compact base set.

Genuine local compactness and regular shrinking give an open neighborhood of the entire
compact set whose closure is compact and lies in the original domain. Actual compact data
bounds give uniform coefficients and linear forcing on that closure and a common time
interval. Apply the actual uniform joint branch theorem on the genuine open neighborhood.
All original equations, smoothness, size, inverse and uniqueness conclusions hold there on
one interval. Neither prior uniform bounds nor any selected-solution continuity is assumed.
Source: the compact-parameter common-interval contraction in `lem:balanced`. -/
theorem balanced_compact_neighborhood_smooth_branch
    {E X Y : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [CompleteSpace Y]
    (Q : X →L[ℝ] X →L[ℝ] Y) (hQ : ∀ x y, Q x y = Q y x)
    (U K : Set E) (hU : IsOpen U) (hK : IsCompact K) (hKU : K ⊆ U)
    (R : ℝ) (hR : 0 < R)
    (A : E × ℝ → Y →L[ℝ] X) (f : E × ℝ → X)
    (hf : ContDiffOn ℝ ∞ f (U ×ˢ Metric.ball (0 : ℝ) R))
    (hA : ContDiffOn ℝ ∞ A (U ×ˢ Metric.ball (0 : ℝ) R))
    (hf0 : ∀ p ∈ U, f (p, 0) = 0) :
    ∃ V : Set E, IsOpen V ∧ K ⊆ V ∧ closure V ⊆ U ∧ IsCompact (closure V) ∧
      ∃ δ C : ℝ, 0 < δ ∧ 0 < C ∧ δ < R ∧ ∃ v : E × ℝ → X,
      ContDiffOn ℝ ∞ v (V ×ˢ Metric.ball (0 : ℝ) δ) ∧
      (∀ p ∈ V, v (p, 0) = 0) ∧
      (∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ,
        v z = f z + A z (Q (v z) (v z)) ∧ ‖v z‖ ≤ C * |z.2| ∧
          ‖(2 : ℝ) • (A z).comp (Q (v z))‖ ≤ 1 / 2 ∧
          (ContinuousLinearMap.id ℝ X - (2 : ℝ) • (A z).comp (Q (v z))).IsInvertible ∧
          ‖(ContinuousLinearMap.id ℝ X - (2 : ℝ) • (A z).comp (Q (v z))).inverse‖ ≤ 2) ∧
      ∀ z ∈ V ×ˢ Metric.ball (0 : ℝ) δ, ∀ w : X,
        w = f z + A z (Q w w) → ‖(2 : ℝ) • (A z).comp (Q w)‖ < 1 → w = v z := by
  obtain ⟨V₀, hV₀, hKV₀, hcomp₀⟩ := exists_isOpen_superset_and_isCompact_closure hK
  obtain ⟨W, hW, hKW, hWU⟩ := hK.exists_isOpen_closure_subset (hU.mem_nhdsSet.mpr hKU)
  let V := V₀ ∩ W
  have hV : IsOpen V := hV₀.inter hW
  have hKV : K ⊆ V := fun p hp ↦ ⟨hKV₀ hp, hKW hp⟩
  have hclU : closure V ⊆ U := (closure_mono inter_subset_right).trans hWU
  have hclcomp : IsCompact (closure V) :=
    hcomp₀.of_isClosed_subset isClosed_closure (closure_mono inter_subset_left)
  obtain ⟨r, L, Cf, hr, hrR, hL, hCf, hdata⟩ := balanced_compact_data_uniform_bounds
    U (closure V) hU hclcomp hclU R hR A f hA.continuousOn
    (hf.of_le (by norm_num)) (fun p hp ↦ hf0 p (hclU hp))
  have hsub : V ×ˢ Metric.ball (0 : ℝ) r ⊆ U ×ˢ Metric.ball (0 : ℝ) R := by
    intro z hz
    exact ⟨hclU (subset_closure hz.1), Metric.ball_subset_ball hrR.le hz.2⟩
  have hclosed (z : E × ℝ) (hz : z ∈ V ×ˢ Metric.ball (0 : ℝ) r) :
      z ∈ closure V ×ˢ Metric.closedBall (0 : ℝ) r :=
    ⟨subset_closure hz.1, Metric.ball_subset_closedBall hz.2⟩
  obtain ⟨δ, C, hδ, hC, hδr, v, hv, hv0, hspec, huniq⟩ :=
    balanced_uniform_joint_smooth_branch Q hQ V hV r hr A f Cf
      ⟨L, fun z hz ↦ (hdata z (hclosed z hz)).1⟩
      (fun z hz ↦ (hdata z (hclosed z hz)).2) (hf.mono hsub) (hA.mono hsub)
  exact ⟨V, hV, hKV, hclU, hclcomp, δ, C, hδ, hC, hδr.trans_lt hrR,
    v, hv, hv0, hspec, huniq⟩

#print axioms balanced_compact_neighborhood_smooth_branch

end GlobalEmbedding.Paper
