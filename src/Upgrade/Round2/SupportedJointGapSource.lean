import Round2.GaugeIncidenceZeros
import Upgrade.IncidenceSupportedSourceResponse

/-!
# Actual n = 3 joint source response at a supported zero

Only the derivative of the SAME supported equation composed with the actual
form is needed. At a true equation zero the proved gauge cancellation controls
this composite using C³ and the genuine metric tangent left inverse. No bound
for the spatial derivative of the chosen normal identification is assumed.
Both actual source endpoints and the original source-frame normalization stay
in the existing incidence and source-response identities.
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

private noncomputable local instance supportedGapSourceFormNormed (F₀ : M → V) (x : M) :
    NormedAddCommGroup (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance supportedGapSourceFormSpace (F₀ : M → V) (x : M) :
    NormedSpace ℝ (SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x) :=
  ContinuousLinearMap.toNormedSpace

/-- The source response is controlled at actual supported zeros, using the
same equation and actual map. The value component retains the old fixed
variation and the actual original C² displacement. -/
theorem SupportedJointPreparedNeighborhood.actual_prepared_source_response_at_supported_zero
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (Dmax Kbound : ℝ)
    (hK : ‖probeAtlasTangentLeftInverse A (probe.map t u) i zy.1‖ ≤ Kbound) :
    let hxc := hA.support_subset i (interior_subset hx)
    let C := actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u, A.chart i zy.1)
    let data := p.probeData hA i hxc probe t j
    C ∈ p.chart.domain → p.chart.equation C = 0 →
    ‖fderiv ℝ p.chart.equation C‖ ≤ Dmax → ∀ v : E,
      ‖fderiv ℝ (fun s ↦ data.incidence (u, s, A.chart j zy.2))
          (A.chart i zy.1) (data.a • v) -
        (0, p.sourceReferenceDerivative A hA i hxc v)‖ ≤
      max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| *
          (Dmax * probe.gaugeSpatialBound hA i x hxc Kbound))
        (probeAtlasDerivativeConstant n N 1 *
          (probe.constant * t ^ ((44 : ℝ) / 5)) + prep.tolerance / 4) * ‖v‖ := by
  intro hxc C data hdom hzero hD v
  have hz : zy.1 ∈ A.support i := interior_subset (prep.support zy hzy)
  have hR := (p.chart.contDiffOn_equation.contDiffAt
    (p.chart.isOpen_domain.mem_nhds hdom)).differentiableAt (by simp)
  have hgap : ‖(normalSpace (I := IM) F₀ zy.1).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1 :=
    (prep.normal_gap zy hzy).trans (by norm_num)
  have hB := probe.actual_supported_source_derivative_bound_at_zero himm₀ hA i x hxc
    t ht htt u hu zy.1 hz hgap p.chart Kbound hK hdom hzero
  have hKnonneg : 0 ≤ Kbound := (norm_nonneg _).trans hK
  have hcomposite : ‖(fderiv ℝ p.chart.equation C).comp
      (fderiv ℝ (fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t)
        (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hxc (u,s))
        (A.chart i zy.1))‖ ≤ Dmax * probe.gaugeSpatialBound hA i x hxc Kbound :=
    hB.trans (mul_le_mul_of_nonneg_right hD
      (probe.gaugeSpatialBound_nonneg hA i x hxc hKnonneg))
  have hraw := probe.actual_source_incidence_error hA t ht htt u hu i x hxc zy.1 zy.2 hz
    p.chart.equation (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5))
    (Real.rpow_pos_of_pos ht _).ne' (Dmax * probe.gaugeSpatialBound hA i x hxc Kbound)
    (prep.tolerance / 4) (prep.source_variation zy hzy).le hR hcomposite v
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

#print axioms SupportedJointPreparedNeighborhood.actual_prepared_source_response_at_supported_zero
end GlobalEmbedding.Upgrade
