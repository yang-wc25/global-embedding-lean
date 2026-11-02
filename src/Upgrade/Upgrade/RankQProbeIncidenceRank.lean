import Upgrade.RankQProbeParameterBounds
import Upgrade.RankQProbeSourceColumns
import Upgrade.RankQPreparedIncidenceRank
import Upgrade.CompactRankQSchurPreparation

/-!
# Actual rank-q joint incidence rank from the full probe estimates

The actual Schur block and derivative margin are derived from the preselected
geometric form ball and the actual new-to-reference displacement. The finite
principal frame is the same fixed-weight frame used before the finite cover.
The remaining displayed bounds are genuine quantitative displacement/source
budgets, not incidence-rank hypotheses.
-/
noncomputable section
open Function Manifold Module Set
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

/-- The actual joint derivative has rank at least 2n+1 on the unchanged
prepared spatial neighborhood. Its rank is proved from the actual probes,
not supplied. The next consumer obtains these numerical budgets uniformly
from the original eta moduli, C²/C³ and the chosen normal control. -/
private theorem rankQ_actual_rank_from_parameter_response
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin n × Fin 2) → Fin r)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (K : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let Cf := fun v s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (v,s)
    let Dbound := ‖rankQNormalBlock B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    let sigma := t ^ ((44 : ℝ) / 5)
    let a := t ^ ((56 : ℝ) / 5)
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc sigma a
    (rankQBlockA B C).IsInvertible →
    ‖(fderiv ℝ (rankQSchur B) C).comp (fderiv ℝ (Cf u) (A.chart i zy.1))‖ ≤ K →
    (∀ l : Fin n × Fin 2,
      ‖fderiv ℝ (fun v ↦ J (v,A.chart i zy.1,A.chart j zy.2)) u
        (probe.rankQPreparationDirection labels t zy.1 l) -
      rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
        (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)‖ ≤
        prep.principal.tolerance) →
    max (|a / sigma| * K) (probeAtlasDerivativeConstant n N 1 *
      (probe.constant * sigma) + prep.principal.tolerance / 4) ≤ prep.principal.tolerance →
    2 * n + 1 ≤ finrank ℝ (fderiv ℝ J (u,A.chart i zy.1,A.chart j zy.2)).range := by
  intro hxc B C Cf Dbound amp sigma a J hblock hK hp hsBudget
  have hpr := prep.subset_principal hzy
  have hz : zy.1 ∈ A.support i := interior_subset (prep.principal.support zy hpr)
  have hzs := hA.support_subset i hz
  have hchart : Cf u (A.chart i zy.1) = C := by
    change projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x ((A.chart i).symm (A.chart i zy.1))
      (probeAtlasNormalizedFrame A hA i x hxc ((A.chart i).symm (A.chart i zy.1))) = _
    rw [(A.chart i).left_inv hzs]
  have hblockChart : (rankQBlockA B (Cf u (A.chart i zy.1))).IsInvertible := by
    rw [hchart]
    exact hblock
  have hJ := probe.toProbeGeometry.actual_rankQ_incidence_differentiable hF₀ A hA i j x hxc
    t ht htt u hu (A.chart i zy.1) (A.chart j zy.2)
    ((A.chart i).map_source hzs) ((A.chart j).map_source hy) sigma a hblockChart
  have hKchart : ‖(fderiv ℝ (rankQSchur B) (Cf u (A.chart i zy.1))).comp
      (fderiv ℝ (Cf u) (A.chart i zy.1))‖ ≤ K := by
    rw [hchart]
    exact hK
  have hs (v : E) := probe.rankQ_prepared_source_response prep.principal
    t ht htt u hu zy hpr j hy K hblockChart hKchart v
  have hs' (v : E) :
      ‖fderiv ℝ (fun s ↦ J (u,s,A.chart j zy.2)) (A.chart i zy.1) (a • v) -
        (0, probeAtlasFirstJet A F₀ i x v)‖ ≤ prep.principal.tolerance * ‖v‖ :=
    (hs v).trans (mul_le_mul_of_nonneg_right hsBudget (norm_nonneg v))
  have hr := prep.principal.actual_joint_rank_of_response
    (probe.map t) (probe.slice_smooth t) (probe.normalIdentification t) j sigma a
    (u,A.chart i zy.1,A.chart j zy.2) hJ
    (probe.rankQPreparationDirection labels t zy.1) hp hs'
  exact hr

/-- The actual joint derivative has rank at least 2n+1 on the unchanged
prepared spatial neighborhood. Its rank is proved from the actual probes,
not supplied. The next consumer obtains these numerical budgets uniformly
from the original eta moduli, C²/C³ and the chosen normal control. -/
theorem RankQSchurPreparedNeighborhood.exact_probe_joint_rank
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves)
    (labels : (Fin n × Fin 2) → Fin r) (hinj : Injective labels)
    (hlabels : ∀ l, waves (labels l) = p.waves l.1)
    (t : ℝ) (ht : 0 < t) (htt : t < probe.threshold)
    (u : ProbeParameters r) (hu : ‖u‖ < probe.radius)
    (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) (K : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let Cf := fun v s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (v,s)
    let Dbound := ‖rankQNormalBlock B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    let sigma := t ^ ((44 : ℝ) / 5)
    let a := t ^ ((56 : ℝ) / 5)
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc sigma a
    ‖C - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ ≤ prep.formBall.radius / 2 →
    ‖(fderiv ℝ (rankQSchur B) C).comp (fderiv ℝ (Cf u) (A.chart i zy.1))‖ ≤ K →
    amp * max (4 * Dbound * ((probe.etaB t + probe.constant * ‖u‖) *
        ‖probeAtlasNormalizationSquare A hA i x hxc‖))
      (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.principal.tolerance / 4 →
    max (|a / sigma| * K) (probeAtlasDerivativeConstant n N 1 *
      (probe.constant * sigma) + prep.principal.tolerance / 4) ≤ prep.principal.tolerance →
    2 * n + 1 ≤ finrank ℝ (fderiv ℝ J (u,A.chart i zy.1,A.chart j zy.2)).range := by
  intro hxc B C Cf Dbound amp sigma a J hnew hK hpBudget hsBudget
  obtain ⟨hblock, hp⟩ := prep.exact_probe_parameter_bounds probe labels hinj hlabels
    t ht htt u hu zy hzy j hy hnew hpBudget
  exact rankQ_actual_rank_from_parameter_response prep probe labels
    t ht htt u hu zy hzy j hy K hblock hK hp hsBudget

#print axioms RankQSchurPreparedNeighborhood.exact_probe_joint_rank
end GlobalEmbedding.Upgrade
