import Upgrade.RankQNativeProbeResponse
import Upgrade.RankQProbeRegularity
import Upgrade.RankQActualSlice

/-! The actual native response is transported through the exact two-chart
parameter slice of the same global map. Both endpoints remain literal. -/
noncomputable section
open Function Manifold Module Set GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] actualResidualNormedAddCommGroup actualResidualNormedSpace
  actualResidualFiniteDimensional actualJointNorm rankQActualDerivativeNorm

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Literal parameter response in two actual atlas charts. Both global value
remainders are retained by the full-probe consumer. The zero derivative-
variation input means its output is the CURRENT Schur principal column. -/
theorem ExactProbeFamily.rankQ_current_principal_response
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (l : Fin r) (i j : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (z y : M) (hz : z ∈ A.support i) (hy : y ∈ (A.chart j).source)
    (haway : (waves l).cutoff y = 0) :
    let B := rankQActualReference F₀ hF₀ x
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x z (probeAtlasNormalizedFrame A hA i x hx z)
    let D := fderiv ℝ (rankQSchur B) C
    let T := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z))
    let sigma := t ^ ((44 : ℝ) / 5)
    let a := t ^ ((56 : ℝ) / 5)
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hx sigma a
    (rankQBlockA B C).IsInvertible →
    ‖fderiv ℝ (fun v ↦ J (v, A.chart i z, A.chart j y)) u
        (probe.rankQRadialDirection t z l) -
      (D T, -((probe.weight l ^ 2)⁻¹) • (waves l).value z)‖ ≤
      max (4 * ‖D‖ * ((probe.etaB t + probe.constant * ‖u‖) *
          ‖probeAtlasNormalizationSquare A hA i x hx‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖)) := by
  intro B C D T sigma a J hblock
  have hraw := probe.rankQ_native_current_principal_response hA t ht htt u hu
    l i j x hx z y hz hy haway hblock
  let Cf := fun v q ↦ projectedIdentifiedTrueForm F₀ (probe.map t v) (probe.slice_smooth t v)
    (probe.normalIdentification t v) x q (probeAtlasNormalizedFrame A hA i x hx q)
  have hslice : (fun v ↦ J (v, A.chart i z, A.chart j y)) =
      (fun v ↦ scaledIncidence Cf (probe.map t) (probe.map t)
        (rankQSchur B) sigma a v z y) :=
    actualRankQJointIncidence_parameterSlice F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hx sigma a z y (hA.support_subset i hz) hy
  have heq := congrArg
    (fun f : ProbeParameters r → (B.ker →L[ℝ] B.rangeᗮ) × V ↦
      ‖fderiv ℝ f u (probe.rankQRadialDirection t z l) -
        (D T, -((probe.weight l ^ 2)⁻¹) • (waves l).value z)‖) hslice
  exact heq.trans_le hraw

#print axioms ExactProbeFamily.rankQ_current_principal_response
end GlobalEmbedding.Upgrade
