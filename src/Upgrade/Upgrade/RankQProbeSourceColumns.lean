import Upgrade.RankQProbeSourceResponse
import Upgrade.RankQActualSourceSlice
import Upgrade.CompactRankQPreparation

/-! Actual first-source columns of the same literal rank-q incidence,
using original C² control and the preselected actual first-jet neighborhood. -/
noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] actualResidualNormedAddCommGroup actualResidualNormedSpace
  actualResidualFiniteDimensional actualJointNorm

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Original C² closeness supplies the value part of the actual source error.
The displayed K bounds the actual equation-source derivative, including all
normal-identification and source-frame variation. -/
theorem ExactProbeFamily.rankQ_prepared_source_response
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (K : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let C := fun v s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (v,s)
    let sigma := t ^ ((44 : ℝ) / 5)
    let a := t ^ ((56 : ℝ) / 5)
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc sigma a
    (rankQBlockA B (C u (A.chart i zy.1))).IsInvertible →
    ‖(fderiv ℝ (rankQSchur B) (C u (A.chart i zy.1))).comp
      (fderiv ℝ (C u) (A.chart i zy.1))‖ ≤ K →
    ∀ v : E,
      ‖fderiv ℝ (fun s ↦ J (u,s,A.chart j zy.2)) (A.chart i zy.1) (a • v) -
        (0, probeAtlasFirstJet A F₀ i x v)‖ ≤
        max (|a / sigma| * K)
          (probeAtlasDerivativeConstant n N 1 * (probe.constant * sigma) + prep.tolerance / 4) * ‖v‖ := by
  intro hxc B C sigma a J hblock hK v
  have hz : zy.1 ∈ A.support i := interior_subset (prep.support zy hzy)
  have hR := (rankQSchur_contDiffAt B (C u (A.chart i zy.1)) hblock).differentiableAt (by simp)
  have hraw := probe.actual_source_incidence_error hA t ht htt u hu i x hxc zy.1 zy.2 hz
    (R := B.ker →L[ℝ] B.rangeᗮ) (rankQSchur B) sigma a
    (Real.rpow_pos_of_pos ht _).ne' K (prep.tolerance / 4)
    (prep.source_variation zy hzy).le hR hK v
  have hslice : (fun s ↦ J (u,s,A.chart j zy.2)) =
      (fun s ↦ scaledIncidence C (fun w q ↦ probe.map t w ((A.chart i).symm q))
        (probe.map t) (rankQSchur B) sigma a u s zy.2) :=
    actualRankQJointIncidence_sourceSlice F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc sigma a u zy.2 hy
  have heq := congrArg
    (fun f : E → (B.ker →L[ℝ] B.rangeᗮ) × V ↦
      ‖fderiv ℝ f (A.chart i zy.1) (a • v) - (0, probeAtlasFirstJet A F₀ i x v)‖) hslice
  exact heq.trans_le hraw

#print axioms ExactProbeFamily.rankQ_prepared_source_response
end GlobalEmbedding.Upgrade
