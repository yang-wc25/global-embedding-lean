import Round2.SupportedJointGapSource
import Upgrade.IncidenceSupportedProbeRank

/-!
# Actual supported joint rank at the incidence zeros, without spatial DQ

The unchanged parameter response, unequal-weight simulation and prepared
finite frame are reused. The source response now uses the proved composite
equation derivative at a supported zero. Rank is asserted there only, which is
the condition needed by local finite-parameter avoidance.
-/

noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology BigOperators
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
attribute [local instance] incidenceActualFormNormed incidenceActualFormSpace

/-- The literal actual derivative has the prepared rank at every supported
zero satisfying the actual response margins. The margins themselves are
discharged uniformly by `SupportedJointGapUniform`. -/
theorem SupportedJointPreparedNeighborhood.exact_probe_joint_rank_at_supported_zero
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀}
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin (n * (n - 1) / 2 + n) × Fin 2) → Fin r)
    (hinj : Injective labels) (hlabels : ∀ l, waves (labels l) = p.waves l.1)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (Kbound : ℝ)
    (hK : ‖probeAtlasTangentLeftInverse A (probe.map t u) i zy.1‖ ≤ Kbound) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let Dmax := ‖fderiv ℝ p.chart.equation B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    ‖C - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ ≤ prep.formBall.radius / 2 →
    amp * max (4 * Dmax * ((probe.etaB t + probe.constant * ‖u‖) *
        ‖probeAtlasNormalizationSquare A hA i x hxc‖))
      (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.tolerance / 4 →
    max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| *
        (Dmax * probe.gaugeSpatialBound hA i x hxc Kbound))
      (probeAtlasDerivativeConstant n N 1 *
        (probe.constant * t ^ ((44 : ℝ) / 5)) + prep.tolerance / 4) ≤ prep.tolerance →
    p.chart.equation C = 0 → prep.ActualProbeJointRank probe t u zy j := by
  intro hxc B C Dmax amp hnew hparam hsource hzero
  let data := p.probeData hA i hxc probe t j
  obtain ⟨hdom, hD, hp⟩ :=
    @SupportedJointPreparedNeighborhood.exact_probe_parameter_bounds n N M _ _ _ _
      A hA F₀ hF₀ x y₀ p i hx prep r waves probe labels hinj hlabels
      t ht htt u hu zy hzy j hy hnew hparam
  have hz := hA.support_subset i (interior_subset (prep.support zy hzy))
  have hC : actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1) = C := by
    change projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x ((A.chart i).symm (A.chart i zy.1))
      (probeAtlasNormalizedFrame A hA i x hxc ((A.chart i).symm (A.chart i zy.1))) = _
    rw [(A.chart i).left_inv hz]
  have hdom' : actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1) ∈ p.chart.domain := by
    rw [hC]
    exact hdom
  have hD' : ‖fderiv ℝ p.chart.equation (actualSupportedProbeCoordinate F₀ (probe.map t)
      (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hxc
      (u,A.chart i zy.1))‖ ≤ Dmax := by rw [hC]; exact hD
  have hzero' : p.chart.equation (actualSupportedProbeCoordinate F₀ (probe.map t)
      (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hxc
      (u,A.chart i zy.1)) = 0 := by rw [hC]; exact hzero
  have hJ := p.probeData_differentiable hA i hxc probe t ht htt u hu j
    (A.chart i zy.1) (A.chart j zy.2) ((A.chart i).map_source hz)
    ((A.chart j).map_source hy) hdom'
  have hs (v : E) := prep.actual_prepared_source_response_at_supported_zero himm₀ probe
    t ht htt u hu zy hzy j hy Dmax Kbound hK hdom' hzero' hD' v
  have hs' (v : E) :
      ‖fderiv ℝ (fun s ↦ data.incidence (u,s,A.chart j zy.2)) (A.chart i zy.1) (data.a • v) -
        (0, p.sourceReferenceDerivative A hA i hxc v)‖ ≤ prep.tolerance * ‖v‖ :=
    (hs v).trans (mul_le_mul_of_nonneg_right hsource (norm_nonneg v))
  exact prep.actual_joint_rank_of_response data
    (u,A.chart i zy.1,A.chart j zy.2) hJ
    (probe.supportedPreparationDirection labels t zy.1) hp hs'

#print axioms SupportedJointPreparedNeighborhood.exact_probe_joint_rank_at_supported_zero
end GlobalEmbedding.Upgrade
