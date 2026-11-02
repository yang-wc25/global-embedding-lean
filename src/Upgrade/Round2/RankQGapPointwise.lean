import Upgrade.RankQUniformActualRank
import Upgrade.RankQProbeIncidenceRank

/-!
# Rank of the literal rank-q incidence at actual zeros, without a spatial DQ bound

The same prepared spatial neighborhood retains the actual invertible block.
The joint derivative rank is derived only at zeros of the literal incidence,
which is exactly what the accepted avoidance theorem consumes. The normal
identification supplies only its zeroth-order gap; all source bounds follow
from actual C³, target-orbit cancellation and exact-metric tangent splitting.
-/
noncomputable section
open Function Manifold Module Set
open scoped ContDiff Topology
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

/-- Pointwise use of the actual numerical budgets. The source budget is
needed only at a Schur zero; the rank is concluded from the existing concrete
parameter and tangent columns. This lemma isolates elaboration work while
retaining the default checker limits. -/
theorem RankQSchurPreparedNeighborhood.rank_at_schur_zero_of_actual_budgets
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
    (zy : M × M) (hzy : zy ∈ prep.neighborhood) (Ksource : ℝ) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    let C := fun s ↦ actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u,s)
    let Dbound := ‖rankQNormalBlock B‖ + prep.derivativeTolerance
    let amp := rankQWeightSimulationBound (fun k b ↦ probe.weight (labels (k,b))) rankQPreparationWeights
    ‖C (A.chart i zy.1) - normalizedReferenceForm A hA F₀ i x hxc zy.1‖ < prep.formBall.radius / 2 →
    (rankQSchur B (C (A.chart i zy.1)) = 0 →
      ‖(fderiv ℝ (rankQSchur B) (C (A.chart i zy.1))).comp
        (fderiv ℝ C (A.chart i zy.1))‖ ≤ Ksource) →
    amp * max (4 * Dbound * ((probe.etaB t + probe.constant * ‖u‖) *
        ‖probeAtlasNormalizationSquare A hA i x hxc‖))
      (4 * (probe.etaV t + probe.constant * ‖u‖)) ≤ prep.principal.tolerance / 4 →
    max (|t ^ ((56 : ℝ) / 5) / t ^ ((44 : ℝ) / 5)| * Ksource)
      (probeAtlasDerivativeConstant n N 1 * (probe.constant * t ^ ((44 : ℝ) / 5)) +
        prep.principal.tolerance / 4) ≤ prep.principal.tolerance →
    (rankQBlockA B (C (A.chart i zy.1))).IsInvertible ∧
      (rankQSchur B (C (A.chart i zy.1)) = 0 →
        ∀ j : Fin A.count, zy.2 ∈ (A.chart j).source →
          2 * n + 1 ≤ finrank ℝ (fderiv ℝ
            (actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
              (probe.normalIdentification t) A hA i j x hxc
              (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)))
            (u,A.chart i zy.1,A.chart j zy.2)).range) := by
  intro hxc B C Dbound amp hclose hsource hparameter hscaledSource
  have hz : zy.1 ∈ (A.chart i).source := hA.support_subset i
    (interior_subset (prep.principal.support zy (prep.subset_principal hzy)))
  have hchart : C (A.chart i zy.1) =
      projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
        (probe.normalIdentification t u) x zy.1
        (probeAtlasNormalizedFrame A hA i x hxc zy.1) := by
    change projectedIdentifiedTrueForm _ _ _ _ _ ((A.chart i).symm (A.chart i zy.1))
      (probeAtlasNormalizedFrame _ _ _ _ _ ((A.chart i).symm (A.chart i zy.1))) = _
    rw [(A.chart i).left_inv hz]
  have hnear : ‖C (A.chart i zy.1) - B‖ < prep.formBall.radius := by
    have htri := norm_sub_le_norm_sub_add_norm_sub (C (A.chart i zy.1))
      (normalizedReferenceForm A hA F₀ i x hxc zy.1) B
    have href := prep.reference_variation zy hzy
    linarith
  refine ⟨(prep.formBall.spec _ hnear).1, ?_⟩
  intro hzero j hy
  apply prep.exact_probe_joint_rank probe labels hinj hlabels t ht htt u hu zy hzy j hy Ksource
  · simpa only [hchart] using hclose.le
  · simpa only [hchart] using hsource hzero
  · exact hparameter
  · exact hscaledSource

#print axioms RankQSchurPreparedNeighborhood.rank_at_schur_zero_of_actual_budgets
end GlobalEmbedding.Upgrade
