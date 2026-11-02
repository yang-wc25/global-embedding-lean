import Upgrade.RankQUniformProbeControl
import Upgrade.RankQProbeIncidenceRank

/-!
# Uniform rank of the literal rank-q probe incidence

The already chosen spatial neighborhood is kept fixed.  Full probes and the
chosen normal control give a parameter ball and a scale on which the actual
Schur block is invertible and the actual joint derivative has rank at least
`2*n+1`, for either independent chart at the second source point.
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

/-- Actual, uniform joint rank.  The only construction dependency besides the
complete probes is the quantitative control of its same chosen normal
identification, explicitly represented by `ChosenProbeNormalControl`. -/
theorem RankQSchurPreparedNeighborhood.exists_probe_ball_scale_rank
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalControl probe)
    (labels : (Fin n × Fin 2) → Fin r) (hinj : Injective labels)
    (hlabels : ∀ l, waves (labels l) = p.waves l.1) :
    let hxc := hA.support_subset i (interior_subset hx)
    let B := rankQActualReference F₀ hF₀ x
    ∃ rho > 0, rho ≤ probe.radius ∧ ∃ t₀ > 0, t₀ ≤ probe.threshold ∧
      ∀ t, 0 < t → t < t₀ → ∀ u : ProbeParameters r, ‖u‖ < rho →
      ∀ zy ∈ prep.neighborhood,
      (rankQBlockA B (actualSupportedProbeCoordinate F₀ (probe.map t)
        (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hxc
        (u,A.chart i zy.1))).IsInvertible ∧
      ∀ j : Fin A.count, zy.2 ∈ (A.chart j).source →
        2 * n + 1 ≤ finrank ℝ (fderiv ℝ
          (actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
            (probe.normalIdentification t) A hA i j x hxc
            (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)))
          (u,A.chart i zy.1,A.chart j zy.2)).range := by
  intro hxc B
  obtain ⟨rho, hrho, hrhoBound, tau, htau, htauBound, hbud⟩ :=
    prep.exists_probe_ball_scale_budgets hcompact probe control labels
  refine ⟨rho, hrho, hrhoBound, tau, htau, htauBound, ?_⟩
  intro t ht htt u hu zy hzy
  have hz : zy.1 ∈ (A.chart i).source := hA.support_subset i
    (interior_subset (prep.principal.support zy (prep.subset_principal hzy)))
  have hchart : actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1) =
      projectedIdentifiedTrueForm F₀ (probe.map t u) (probe.slice_smooth t u)
        (probe.normalIdentification t u) x zy.1
        (probeAtlasNormalizedFrame A hA i x hxc zy.1) := by
    change projectedIdentifiedTrueForm _ _ _ _ _ ((A.chart i).symm (A.chart i zy.1))
      (probeAtlasNormalizedFrame _ _ _ _ _ ((A.chart i).symm (A.chart i zy.1))) = _
    rw [(A.chart i).left_inv hz]
  have hbudget := hbud t ht htt u hu zy hzy
  have hnear : ‖actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
      (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1) - B‖ <
      prep.formBall.radius := by
    have htri := norm_sub_le_norm_sub_add_norm_sub
      (actualSupportedProbeCoordinate F₀ (probe.map t) (probe.slice_smooth t)
        (probe.normalIdentification t) A hA i x hxc (u,A.chart i zy.1))
      (normalizedReferenceForm A hA F₀ i x hxc zy.1) B
    have href := prep.reference_variation zy hzy
    linarith [hbudget.1]
  refine ⟨(prep.formBall.spec _ hnear).1, ?_⟩
  intro j hy
  apply prep.exact_probe_joint_rank probe labels hinj hlabels t ht
    (htt.trans_le htauBound) u (hu.trans_le hrhoBound) zy hzy j hy
    ((‖rankQNormalBlock B‖ + prep.derivativeTolerance) *
      control.coordinateSpatialBound hA i x hxc)
  · simpa only [hchart] using hbudget.1.le
  · simpa only [hchart] using hbudget.2.1
  · exact hbudget.2.2.1
  · exact hbudget.2.2.2

#print axioms RankQSchurPreparedNeighborhood.exists_probe_ball_scale_rank
end GlobalEmbedding.Upgrade
