import Upgrade.IncidenceSupportedProbeData
import Upgrade.IncidenceSpatialBound
import Upgrade.CompactSupportedJointPreparation

/-!
# The literal supported joint incidence: complete first-source error

The C³ estimate controls the derivative of its actual identified Hessian,
including source frame variation and the spatial derivative of Q. The value
component uses the original C² distance and the fixed atlas first jet. No
fast-angle combination is differentiated.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

private noncomputable local instance supportedSourceFormNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance supportedSourceFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

theorem SupportedJointWavePacket.sourceReferenceDerivative_eq_firstJet
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y : M}
    (p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (hx : x ∈ (A.chart i).source) :
    p.sourceReferenceDerivative A hA i hx = probeAtlasFirstJet A F₀ i x := by
  rw [probeAtlasFirstJet_eq_mfderiv_frame A hA F₀ hF₀ i x hx]
  rw [SupportedJointWavePacket.sourceReferenceDerivative,
    probeAtlasInverseFrameEquiv_toContinuousLinearMap]
  rfl

/-- This is the actual first-source derivative of the same two-chart
supported coincidence function, with its full C³ contribution displayed. -/
theorem SupportedJointPreparedNeighborhood.actual_prepared_source_response
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalControl probe)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (Dmax : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u, A.chart i zy.1)
    let data := p.probeData hA i hxc probe t j
    C ∈ p.chart.domain → ‖fderiv ℝ p.chart.equation C‖ ≤ Dmax →
    ∀ v : E,
      ‖fderiv ℝ (fun s ↦ data.incidence (u, s, A.chart j zy.2))
          (A.chart i zy.1) (data.a • v) -
        (0, p.sourceReferenceDerivative A hA i hxc v)‖ ≤
      max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| *
          (Dmax * control.coordinateSpatialBound hA i x hxc))
        (probeAtlasDerivativeConstant n N 1 *
          (probe.constant * t ^ ((44 : ℝ) / 5)) + prep.tolerance / 4) * ‖v‖ := by
  intro hxc C data hdom hD v
  have hz : zy.1 ∈ A.support i := interior_subset (prep.support zy hzy)
  have hR := (p.chart.contDiffOn_equation.contDiffAt
    (p.chart.isOpen_domain.mem_nhds hdom)).differentiableAt (by simp)
  have hB := control.actual_coordinate_spatial_bound hA i x hxc t ht htt u hu zy.1 hz
  have hDnonneg : 0 ≤ Dmax := (norm_nonneg _).trans hD
  have hK : ‖(fderiv ℝ p.chart.equation C).comp
      (fderiv ℝ (fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t)
        (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hxc (u,s))
        (A.chart i zy.1))‖ ≤ Dmax * control.coordinateSpatialBound hA i x hxc :=
    (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul hD hB (norm_nonneg _) hDnonneg)
  have hraw := probe.actual_source_incidence_error hA t ht htt u hu i x hxc zy.1 zy.2 hz
    p.chart.equation (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5))
    (Real.rpow_pos_of_pos ht _).ne' (Dmax * control.coordinateSpatialBound hA i x hxc)
    (prep.tolerance / 4) (prep.source_variation zy hzy).le hR hK v
  have hslice : (fun s ↦ data.incidence (u, s, A.chart j zy.2)) =
      (fun s ↦ scaledIncidence
        (fun v q ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
          (probe.normalIdentification t) A hA i x hxc (v,q))
        (fun v q ↦ probe.map t v ((A.chart i).symm q)) (probe.map t)
        p.chart.equation (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)) u s zy.2) := by
    funext s
    simp only [data, SupportedJointWavePacket.IncidenceData.incidence,
      SupportedJointWavePacket.probeData, SupportedJointWavePacket.actualIncidence,
      jointScaledIncidence, scaledIncidence, (A.chart j).left_inv hy]
  have hsliceD := congrArg
    (fun f : E → (Fin p.chart.codim → ℝ) × V ↦
      fderiv ℝ f (A.chart i zy.1) (data.a • v)) hslice
  have href := congrArg (fun L : E →L[ℝ] V ↦ L v)
    (p.sourceReferenceDerivative_eq_firstJet A hA i hxc)
  have heq := congrArg₂ (fun a b : (Fin p.chart.codim → ℝ) × V ↦ ‖a - b‖)
    hsliceD (congrArg (fun q : V ↦ ((0 : Fin p.chart.codim → ℝ), q)) href)
  exact heq.trans_le hraw

#print axioms SupportedJointWavePacket.sourceReferenceDerivative_eq_firstJet
#print axioms SupportedJointPreparedNeighborhood.actual_prepared_source_response
end GlobalEmbedding.Upgrade
