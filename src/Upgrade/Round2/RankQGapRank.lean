import Round2.RankQGapControl
import Round2.RankQGapPointwise

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

/-- Uniform actual zero-set rank. No incidence-rank hypothesis, spatial DQ
bound, or parameter-dependent change of prepared neighborhoods is assumed. -/
theorem RankQSchurPreparedNeighborhood.exists_probe_ball_scale_rank_at_zeros_from_gap
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
    (hcompact : ∀ i, IsCompact (A.support i))
    {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
    {p : RankQLocalWavePacket F₀ hF₀ x y₀}
    {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} {waves : Fin r → LocalLegalWave F₀ hF₀}
    (probe : ExactProbeFamily F₀ hF₀ A waves) (control : ChosenProbeNormalGap probe)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
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
      (rankQSchur B (actualSupportedProbeCoordinate F₀ (probe.map t)
        (probe.slice_smooth t) (probe.normalIdentification t) A hA i x hxc
        (u,A.chart i zy.1)) = 0 →
      ∀ j : Fin A.count, zy.2 ∈ (A.chart j).source →
        2 * n + 1 ≤ finrank ℝ (fderiv ℝ
          (actualRankQJointIncidence F₀ hF₀ (probe.map t) (probe.slice_smooth t)
            (probe.normalIdentification t) A hA i j x hxc
            (t ^ ((44 : ℝ) / 5)) (t ^ ((56 : ℝ) / 5)))
          (u,A.chart i zy.1,A.chart j zy.2)).range) := by
  intro hxc B
  obtain ⟨Kbound, hKbound, hK⟩ :=
    exists_uniform_sameMetric_tangentLeftInverse_bound A hA hcompact F₀ hF₀ himm
  obtain ⟨rho, hrho, hrhoBound, tau, htau, htauBound, hbud⟩ :=
    prep.exists_probe_ball_scale_budgets_at_zeros_from_gap hcompact probe control himm
      Kbound hKbound.le (fun G hG hmetric z hz ↦ hK G hG hmetric i z hz) labels
  refine ⟨rho, hrho, hrhoBound, tau, htau, htauBound, ?_⟩
  intro t ht htt u hu zy hzy
  have hbudget := hbud t ht htt u hu zy hzy
  exact prep.rank_at_schur_zero_of_actual_budgets probe labels hinj hlabels t ht
    (htt.trans_le htauBound) u (hu.trans_le hrhoBound) zy hzy
    ((‖rankQNormalBlock B‖ + prep.derivativeTolerance) *
      probe.gaugeSpatialBound hA i x hxc Kbound)
    hbudget.1 hbudget.2.1 hbudget.2.2.1 hbudget.2.2.2

#print axioms RankQSchurPreparedNeighborhood.exists_probe_ball_scale_rank_at_zeros_from_gap
end GlobalEmbedding.Upgrade
