import NormalPolar.ActualRepairParameterBall
import Mathlib.Geometry.Manifold.BumpFunction

/-!
# A genuine global parameter input supported in one actual parameter chart

The closed repair parameter space can be compact.  A chart coordinate is
therefore extended by an actual smooth cutoff before it is used as a global
input.  The construction below keeps the real chart centre, is globally
bounded, and agrees with the coordinate displacement on the inner ball.
No global Euclidean parameter manifold or fictitious chart extension is used.
-/

noncomputable section
open Set Filter Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.NormalPolar

variable {d : ℕ} {P : Type*} [TopologicalSpace P] [T2Space P]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)

def actualParameterChartCutoff
    (B : OpenPartialHomeomorph P Ep) (center : Ep) (f : ContDiffBump center) : P → Ep :=
  fun p => if p ∈ B.source then f (B p) • (B p - center) else 0

theorem actualParameterChartCutoff_support
    (B : OpenPartialHomeomorph P Ep) (center : Ep) (f : ContDiffBump center)
    (hball : Metric.closedBall center f.rOut ⊆ B.target) :
    tsupport (actualParameterChartCutoff B center f) ⊆
      B.symm '' Metric.closedBall center f.rOut := by
  have hclosed : IsClosed (B.symm '' Metric.closedBall center f.rOut) :=
    ((isCompact_closedBall center f.rOut).image_of_continuousOn
      (B.continuousOn_symm.mono hball)).isClosed
  apply closure_minimal _ hclosed
  intro p hp
  have hne : actualParameterChartCutoff B center f p ≠ 0 := hp
  by_cases hs : p ∈ B.source
  · have hf : f (B p) ≠ 0 := by
      intro hz
      apply hne
      simp only [actualParameterChartCutoff, ite_eq_left hs, hz, zero_smul]
    have hb : B p ∈ Metric.ball center f.rOut := by
      rw [← f.support_eq]
      exact hf
    exact ⟨B p, Metric.ball_subset_closedBall hb, B.left_inv hs⟩
  · exact False.elim (hne (by simp only [actualParameterChartCutoff, ite_eq_right hs]))

theorem actualParameterChartCutoff_smooth
    (B : OpenPartialHomeomorph P Ep) (hB : B ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (center : Ep) (f : ContDiffBump center)
    (hball : Metric.closedBall center f.rOut ⊆ B.target) :
    ContMDiff 𝓘(ℝ, Ep) 𝓘(ℝ, Ep) ∞ (actualParameterChartCutoff B center f) := by
  refine contMDiff_of_tsupport fun p hp => ?_
  obtain ⟨z, hz, hpz⟩ := actualParameterChartCutoff_support B center f hball hp
  have hs : p ∈ B.source := by
    rw [← hpz]
    exact B.map_target (hball hz)
  have hchart : ContMDiffAt 𝓘(ℝ, Ep) 𝓘(ℝ, Ep) ∞ B p :=
    (contMDiffOn_of_mem_maximalAtlas hB p hs).contMDiffAt (B.open_source.mem_nhds hs)
  have hlocal : ContMDiffAt 𝓘(ℝ, Ep) 𝓘(ℝ, Ep) ∞
      (fun q => f (B q) • (B q - center)) p :=
    ((f.contDiff.contMDiff.contMDiffAt).comp p hchart).smul (hchart.sub contMDiffAt_const)
  apply hlocal.congr_of_eventuallyEq
  filter_upwards [B.open_source.mem_nhds hs] with q hq
  simp only [actualParameterChartCutoff, ite_eq_left hq]

theorem actualParameterChartCutoff_norm_le
    (B : OpenPartialHomeomorph P Ep) (center : Ep) (f : ContDiffBump center) (p : P) :
    ‖actualParameterChartCutoff B center f p‖ ≤ f.rOut := by
  by_cases hs : p ∈ B.source
  · by_cases hz : f (B p) = 0
    · simpa only [actualParameterChartCutoff, ite_eq_left hs, hz, zero_smul, norm_zero]
        using f.rOut_pos.le
    · have hb : B p ∈ Metric.ball center f.rOut := by
        rw [← f.support_eq]
        exact hz
      have hd : ‖B p - center‖ ≤ f.rOut := by
        simpa only [Metric.mem_ball, dist_eq_norm] using hb.le
      simp only [actualParameterChartCutoff, ite_eq_left hs, norm_smul,
        Real.norm_eq_abs, abs_of_nonneg f.nonneg]
      exact (mul_le_mul_of_nonneg_right f.le_one (norm_nonneg _)).trans
        (by simpa only [one_mul] using hd)
  · simpa only [actualParameterChartCutoff, ite_eq_right hs, norm_zero] using f.rOut_pos.le

theorem actualParameterChartCutoff_coordinates
    (B : OpenPartialHomeomorph P Ep) (center : Ep) (f : ContDiffBump center)
    (hball : Metric.closedBall center f.rOut ⊆ B.target)
    (v : Ep) (hv : ‖v‖ ≤ f.rIn) :
    actualParameterChartCutoff B center f (B.symm (center + v)) = v := by
  have hi : center + v ∈ Metric.closedBall center f.rIn := by
    simpa only [Metric.mem_closedBall, dist_eq_norm, add_sub_cancel_left] using hv
  have ht : center + v ∈ B.target := hball (Metric.closedBall_subset_closedBall f.rIn_lt_rOut.le hi)
  simp only [actualParameterChartCutoff, ite_eq_left (B.map_target ht), B.right_inv ht,
    f.one_of_mem_closedBall hi, one_smul, add_sub_cancel_left]

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.actualParameterChartCutoff_smooth
#print axioms GlobalEmbedding.NormalPolar.actualParameterChartCutoff_norm_le
#print axioms GlobalEmbedding.NormalPolar.actualParameterChartCutoff_coordinates
