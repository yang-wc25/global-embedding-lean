import Upgrade.IncidenceActualProbeErrors
import Upgrade.RankQActualRegularity
import Upgrade.RankQDerivativeNorms
import Upgrade.CompactRankQPreparation

/-!
# Actual native probe columns before the exact chart-slice transport

The two global endpoints occur in the parameter slice of the same actual
incidence. The reference derivative for the raw radial-pair estimate is the
CURRENT Schur derivative. Thus subsequent fixed-weight simulation amplifies
only genuine probe remainders; geometric derivative variation is added after
simulation, with coefficient one, preserving the pre-probe cover.
-/

noncomputable section
open Function Manifold Module Set GlobalEmbedding.Offline
open scoped ContDiff Topology BigOperators
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

private noncomputable local instance rankQCoordinateNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup

private noncomputable local instance rankQCoordinateNormedSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

local instance rankQActualDerivativeNorm
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x : M} :
    Norm ((SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) →L[ℝ]
      (rankQActualReference F₀ hF₀ x).ker →L[ℝ] (rankQActualReference F₀ hF₀ x).rangeᗮ) :=
  (rankQDerivativeNormedAddCommGroup (rankQActualReference F₀ hF₀ x)).toNorm

/-- A pointwise radial direction of the already differentiated actual probe
family. Its fast angle is not differentiated in any subsequent use. -/
def ExactProbeFamily.rankQRadialDirection
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    {A : BufferedAtlas M E} {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (t : ℝ) (z : M) (l : Fin r) :
    ProbeParameters r :=
  pairedRadialDirection (probe.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5))
    (Pi.single (l,false) 1) (Pi.single (l,true) 1)

/-- Literal parameter response in two actual atlas charts. Both global value
remainders are retained by the full-probe consumer. The zero derivative-
variation input means its output is the CURRENT Schur principal column. -/
theorem ExactProbeFamily.rankQ_native_current_principal_response
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
    let Cf := fun v q ↦ projectedIdentifiedTrueForm F₀ (probe.map t v) (probe.slice_smooth t v)
      (probe.normalIdentification t v) x q (probeAtlasNormalizedFrame A hA i x hx q)
    (rankQBlockA B C).IsInvertible →
    ‖fderiv ℝ (fun v ↦ scaledIncidence Cf (probe.map t) (probe.map t)
        (rankQSchur B) sigma a v z y) u
        (probe.rankQRadialDirection t z l) -
      (D T, -((probe.weight l ^ 2)⁻¹) • (waves l).value z)‖ ≤
      max (4 * ‖D‖ * ((probe.etaB t + probe.constant * ‖u‖) *
          ‖probeAtlasNormalizationSquare A hA i x hx‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖)) := by
  intro B C D T sigma a Cf hblock
  have hR := (rankQSchur_contDiffAt B C hblock).differentiableAt (by simp)
  have hraw := probe.actual_paired_incidence_error hA t ht htt u hu l i j x hx z y hz hy haway
    (R := B.ker →L[ℝ] B.rangeᗮ) (rankQSchur B) D 0 hR
    (by change ‖D - D‖ ≤ 0; simp)
  simp only [zero_mul, zero_add] at hraw
  exact hraw

#print axioms ExactProbeFamily.rankQ_native_current_principal_response
end GlobalEmbedding.Upgrade
