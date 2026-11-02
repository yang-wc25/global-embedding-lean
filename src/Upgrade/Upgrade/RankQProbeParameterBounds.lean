import Upgrade.RankQProbeSimulation
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
theorem RankQSchurPreparedNeighborhood.exact_probe_parameter_bounds
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
    (j : Fin A.count) (hy : zy.2 ∈ (A.chart j).source) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let C := projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
      (probe.normalIdentification t u) x zy.1 (probeAtlasNormalizedFrame A hA i x hxc zy.1)
    let Dbound := ‖rankQNormalBlock B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    let sigma := t ^ ((44 : ℝ) / 5)
    let a := t ^ ((56 : ℝ) / 5)
    let J := actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i j x hxc sigma a
    ‖C - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ ≤ prep.formBall.radius / 2 →
    amp * max (4 * Dbound * ((probe.etaB t + probe.constant * ‖u‖) *
        ‖probeAtlasNormalizationSquare A hA i x hxc‖))
      (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.principal.tolerance / 4 →
    (rankQBlockA B C).IsInvertible ∧
    ∀ l : Fin n × Fin 2,
      ‖fderiv ℝ (fun v ↦ J (v,A.chart i zy.1,A.chart j zy.2)) u
        (probe.rankQPreparationDirection labels t zy.1 l) -
      rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
        (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)‖ ≤
        prep.principal.tolerance := by
  intro hxc B C Dbound amp sigma a J hnew hpBudget
  have hpr := prep.subset_principal hzy
  have hz : zy.1 ∈ A.support i := interior_subset (prep.principal.support zy hpr)
  have hzs := hA.support_subset i hz
  have hnear : ‖C - B‖ < prep.formBall.radius := by
    have htri := norm_sub_le_norm_sub_add_norm_sub C
      (normalizedReferenceForm A hA F₀ i x hxc zy.1) B
    have href := prep.reference_variation zy hzy
    linarith
  obtain ⟨hblock, _, hD, hDnorm, _⟩ := prep.formBall.spec C hnear
  have hamp : 0 ≤ amp := (rankQWeightSimulationBound_pos _ _).le
  have hepsB : 0 ≤ (probe.etaB t + probe.constant * ‖u‖) *
      ‖probeAtlasNormalizationSquare A hA i x hxc‖ :=
    mul_nonneg (add_nonneg (probe.etaB_nonneg t)
      (mul_nonneg probe.constant_nonneg (norm_nonneg u))) (norm_nonneg _)
  have hp : ∀ l : Fin n × Fin 2,
      ‖fderiv ℝ (fun v ↦ J (v,A.chart i zy.1,A.chart j zy.2)) u
        (probe.rankQPreparationDirection labels t zy.1 l) -
      rankQActualPrincipalColumn F₀ hF₀ x ((p.waves l.1).tensor x)
        (-((rankQPreparationWeights l.1 l.2 ^ 2)⁻¹) • (p.waves l.1).value x)‖ ≤
        prep.principal.tolerance := by
    intro l
    have hresponse := probe.rankQ_prepared_parameter_response prep.principal labels hinj hlabels
      t ht htt u hu zy hpr j hy prep.derivativeTolerance hblock hD.le l
    have h4 : 4 * ‖fderiv ℝ (rankQSchur B) C‖ ≤ 4 * Dbound :=
      mul_le_mul_of_nonneg_left hDnorm (show (0 : ℝ) ≤ 4 by norm_num)
    have hraw := max_le_max (mul_le_mul_of_nonneg_right h4 hepsB)
      (le_refl (4 * (probe.etaV t + probe.constant * ‖u‖)))
    have hraw' := (mul_le_mul_of_nonneg_left hraw hamp).trans hpBudget
    have hgeom := (mul_le_mul_of_nonneg_left (prep.tensor_bound zy hzy l.1)
      prep.derivativeTolerance_pos.le).trans prep.derivative_budget
    apply hresponse.trans
    have hsum := add_le_add (add_le_add hraw' hgeom)
      (le_refl (prep.principal.tolerance / 4))
    exact hsum.trans (by linarith [prep.principal.tolerance_pos])
  exact ⟨hblock, hp⟩

#print axioms RankQSchurPreparedNeighborhood.exact_probe_parameter_bounds
end GlobalEmbedding.Upgrade
