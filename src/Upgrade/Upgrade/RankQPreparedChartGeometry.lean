import Upgrade.RankQPreparedChartDomain
import Upgrade.RankQLowRankDictionary
import Upgrade.RankQActualRegularity

/-!
# Actual smoothness and exact bad-set dictionary on the prepared chart domain

The same actual probe map, normal identification, normalized source frame and
Schur equation are used for both the smoothness proof and the zero set. No
regularity of a surrogate form field or a supplied incidence rank is needed.
-/
noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] residualNormedAddCommGroup residualNormedSpace

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Smoothness on the actual two-chart pullback of the original fixed
prepared neighborhood. Only the protected actual block is required. -/
theorem RankQSchurPreparedNeighborhood.probe_contDiffOn_coordinateDomain
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (rho : ℝ) (hrho : rho ≤ probe.radius) (j : Fin A.count)
    (sigma a : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    (∀ u : ProbeParameters r, ‖u‖ < rho → ∀ zy ∈ prep.neighborhood,
      (rankQBlockA (rankQActualReference F₀ hF₀ x)
        (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1))).IsInvertible) →
    ContDiffOn ℝ ∞ (actualRankQJointIncidence F₀ hF₀ (probe.map t)
      (probe.slice_smooth t) (probe.normalIdentification t) A hA i j x hxc sigma a)
      (prep.coordinateDomain rho j) := by
  intro hxc hblock
  apply actualRankQJointIncidence_contDiffOn F₀ hF₀ (probe.map t) (probe.slice_smooth t)
    (probe.normalIdentification t) A hA i j x hxc sigma a Metric.isOpen_ball
    (probe.joint_smooth t ht htt) (probe.normalIdentification_smooth t ht htt)
  · intro w hw
    have hm := (prep.mem_coordinateDomain_iff rho j w).mp hw
    refine ⟨?_, hm.2.1, hm.2.2.1⟩
    simpa only [Metric.mem_ball, dist_zero_right] using hm.1.trans_le hrho
  · intro w hw
    have hm := (prep.mem_coordinateDomain_iff rho j w).mp hw
    have hb := hblock w.1 hm.1
      ((A.chart i).symm w.2.1, (A.chart j).symm w.2.2) hm.2.2.2
    simpa only [(A.chart i).right_inv hm.2.1] using hb

/-- Exact rank-at-most-q/coincidence dictionary on the actual prepared
two-chart domain. The lower rank bound comes from the invertible block. -/
theorem RankQSchurPreparedNeighborhood.probe_zero_iff_coordinateDomain
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (hrank : finrank ℝ (trueSecondForm F₀ hF₀ x).range = n * (n - 1) / 2)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t rho : ℝ) (j : Fin A.count) (sigma a : ℝ)
    (hsigma : sigma ≠ 0) (ha : a ≠ 0)
    (w : ProbeParameters r × (E × E)) (hw : w ∈ prep.coordinateDomain rho j) :
    let hxc := hA.support_subset i (interior_subset hx)
    (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hxc (w.1,w.2.1))).IsInvertible →
    (actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc sigma a w = 0 ↔
      finrank ℝ (trueSecondForm (probe.map t w.1) (probe.slice_smooth t w.1)
        ((A.chart i).symm w.2.1)).range ≤ n * (n - 1) / 2 ∧
      probe.map t w.1 ((A.chart i).symm w.2.1) =
        probe.map t w.1 ((A.chart j).symm w.2.2)) := by
  intro hxc hblock
  have hm := (prep.mem_coordinateDomain_iff rho j w).mp hw
  have hgap := prep.normal_gap
    ((A.chart i).symm w.2.1, (A.chart j).symm w.2.2) hm.2.2.2
  exact actualRankQJointIncidence_zero_iff_rank_le F₀ hF₀ himm
    (probe.map t) (probe.slice_smooth t) (probe.normalIdentification t)
    A hA i j x hxc sigma a hsigma ha w hm.2.1 (hgap.trans (by norm_num)) hrank hblock

#print axioms RankQSchurPreparedNeighborhood.probe_contDiffOn_coordinateDomain
#print axioms RankQSchurPreparedNeighborhood.probe_zero_iff_coordinateDomain
end GlobalEmbedding.Upgrade
