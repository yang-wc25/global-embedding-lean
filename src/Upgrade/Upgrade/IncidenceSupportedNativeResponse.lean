import Upgrade.SupportedProbePackets
import Upgrade.IncidenceActualProbeErrors

/-!
# The same exact probe family in the actual supported joint incidence

The data fields below are filled directly from one ExactProbeFamily. The
parameter-slice identity keeps both independently chosen atlas charts and
both actual values. The actual paired-column error is a direct consequence
of the original full response estimates, with the CURRENT equation derivative
as reference. This order lets returned-weight combinations amplify only raw
probe errors, leaving all fixed geometric margins unchanged.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open Paper GlobalEmbedding.Offline SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance supportedProbeFormNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance supportedProbeFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

namespace SupportedJointWavePacket

theorem native_current_principal_response
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀)
    {A : BufferedAtlas M E} (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius) (l : Fin r)
    (j : Fin A.count) (z y : M) (hz : z ∈ A.support i) (hy : y ∈ (A.chart j).source)
    (haway : (waves l).cutoff y = 0) :
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x z (probeAtlasNormalizedFrame A hA i x hx z)
    let T := (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
      (probeTensorInFrame (probeAtlasNormalizedFrame A hA i x hx z) ((waves l).tensor z))
    let D := fderiv ℝ p.chart.equation C
    C ∈ p.chart.domain →
    ‖fderiv ℝ
        (fun v ↦ scaledIncidence
          (fun w q ↦ projectedIdentifiedTrueForm F₀ (probe.map t w) (probe.slice_smooth t w)
            (probe.normalIdentification t w) x q (probeAtlasNormalizedFrame A hA i x hx q))
          (probe.map t) (probe.map t) p.chart.equation
          (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)) v z y) u
        (pairedRadialDirection (probe.weight l * (waves l).phase z / t ^ ((6 : ℝ) / 5))
          (Pi.single (l, false) 1) (Pi.single (l, true) 1)) -
      (D T, -((probe.weight l ^ 2)⁻¹) • (waves l).value z)‖ ≤
      max (4 * ‖D‖ * ((probe.etaB t + probe.constant * ‖u‖) *
          ‖probeAtlasNormalizationSquare A hA i x hx‖))
        (4 * (probe.etaV t + probe.constant * ‖u‖)) := by
  intro C T D hdom
  have hR := (p.chart.contDiffOn_equation.contDiffAt
    (p.chart.isOpen_domain.mem_nhds hdom)).differentiableAt (by simp)
  have hraw := probe.actual_paired_incidence_error hA t ht htt u hu l i j x hx z y hz hy haway
    p.chart.equation D 0 hR (by simp only [D, C, sub_self, norm_zero, le_refl])
  simpa only [zero_mul, zero_add] using! hraw

end SupportedJointWavePacket
#print axioms SupportedJointWavePacket.native_current_principal_response
end GlobalEmbedding.Upgrade
