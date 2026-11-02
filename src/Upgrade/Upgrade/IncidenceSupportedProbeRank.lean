import Upgrade.IncidenceFormNorms
import Upgrade.IncidenceSupportedParameterBounds
import Upgrade.IncidenceSupportedRankAssembly

/-! Full actual probes yield the supported joint incidence rank using the fixed geometric preparation. -/

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

theorem SupportedJointPreparedNeighborhood.exact_probe_joint_rank
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : SupportedJointWavePacket (n := n) (N := N) F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : SupportedJointPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalControl probe)
    (labels : (Fin (n * (n - 1) / 2 + n) × Fin 2) → Fin r)
    (hinj : Injective labels) (hlabels : ∀ l, waves (labels l) = p.waves l.1)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F₀ x from trueSecondForm F₀ hF₀ x)
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let Dmax := ‖fderiv ℝ p.chart.equation B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    let data := p.probeData hA i hxc probe t j
    ‖C - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ ≤ prep.formBall.radius / 2 →
    amp * max (4 * Dmax * ((probe.etaB t + probe.constant * ‖u‖) *
        ‖probeAtlasNormalizationSquare A hA i x hxc‖))
      (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.tolerance / 4 →
    max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| *
        (Dmax * control.coordinateSpatialBound hA i x hxc))
      (probeAtlasDerivativeConstant n N 1 *
        (probe.constant * t ^ ((44 : ℝ) / 5)) + prep.tolerance / 4) ≤ prep.tolerance →
    prep.ActualProbeJointRank probe t u zy j := by
  intro hxc B C Dmax amp data hnew hparam hsource
  obtain ⟨hdom, hD, hp⟩ :=
    @SupportedJointPreparedNeighborhood.exact_probe_parameter_bounds n N M _ _ _ _
      A hA F₀ hF₀ x y₀ p i hx prep r waves probe labels hinj hlabels
      t ht htt u hu zy hzy j hy hnew hparam
  have hr := @SupportedJointPreparedNeighborhood.actual_joint_rank_from_parameter_bound
    n N M _ _ _ _ A hA F₀ hF₀ x y₀ p i hx prep r waves probe control
    t ht htt u hu zy hzy j hy Dmax
    (probe.supportedPreparationDirection labels t zy.1) hdom hD hp hsource
  exact hr

#print axioms SupportedJointPreparedNeighborhood.exact_probe_joint_rank
end GlobalEmbedding.Upgrade
