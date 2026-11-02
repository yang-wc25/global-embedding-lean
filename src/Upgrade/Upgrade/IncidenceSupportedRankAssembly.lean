import Upgrade.IncidenceFormNorms
import Upgrade.IncidenceSupportedSourceResponse
import Upgrade.IncidenceSupportedPreparedRank
import Upgrade.IncidenceSupportedProbeRegularity

/-! Assemble the actual C³ source response with the actual prepared parameter columns. -/

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

/-- A named proposition for the literal actual joint rank; it has no data
fields or assumptions. Sharing this exact expression avoids repeatedly
unfolding the full actual two-chart incidence during elaboration. -/
def SupportedJointPreparedNeighborhood.ActualProbeJointRank
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (t : ℝ) (u : ProbeParameters r)
    (zy : M × M) (j : Fin A.count) : Prop :=
  n * (n - 1) / 2 + 2 * n ≤ finrank ℝ
    (fderiv ℝ (p.probeData hA i (hA.support_subset i (interior_subset hx)) probe t j).incidence
      (u,A.chart i zy.1,A.chart j zy.2)).range

theorem SupportedJointPreparedNeighborhood.actual_joint_rank_from_parameter_bound
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
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (Dmax : ℝ)
    (dirs : (Fin (n * (n - 1) / 2 + n) × Fin 2) → ProbeParameters r) :
    let hxc := hA.support_subset i (interior_subset hx)
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let data := p.probeData hA i hxc probe t j
    C ∈ p.chart.domain → ‖fderiv ℝ p.chart.equation C‖ ≤ Dmax →
    (∀ l, ‖fderiv ℝ (fun v ↦ data.incidence (v,A.chart i zy.1,A.chart j zy.2)) u (dirs l) -
      supportedJointPrincipalColumn (incidenceActualTangent (n := n) F₀ x)
        p.equationColumns p.valueNormals rankQPreparationWeights l‖ ≤ prep.tolerance) →
    max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| *
        (Dmax * control.coordinateSpatialBound hA i x hxc))
      (probeAtlasDerivativeConstant n N 1 *
        (probe.constant * t ^ ((44 : ℝ) / 5)) + prep.tolerance / 4) ≤ prep.tolerance →
    prep.ActualProbeJointRank probe t u zy j := by
  intro hxc C data hdom hD hp hsource
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
  have hJ := p.probeData_differentiable hA i hxc probe t ht htt u hu j
    (A.chart i zy.1) (A.chart j zy.2) ((A.chart i).map_source hz)
    ((A.chart j).map_source hy) hdom'
  have hs (v : E) := prep.actual_prepared_source_response probe control
    t ht htt u hu zy hzy j hy Dmax hdom' hD' v
  have hs' (v : E) :
      ‖fderiv ℝ (fun s ↦ data.incidence (u,s,A.chart j zy.2)) (A.chart i zy.1) (data.a • v) -
        (0, p.sourceReferenceDerivative A hA i hxc v)‖ ≤ prep.tolerance * ‖v‖ :=
    (hs v).trans (mul_le_mul_of_nonneg_right hsource (norm_nonneg v))
  exact prep.actual_joint_rank_of_response data
    (u,A.chart i zy.1,A.chart j zy.2) hJ dirs hp hs'

#print axioms SupportedJointPreparedNeighborhood.actual_joint_rank_from_parameter_bound
end GlobalEmbedding.Upgrade
