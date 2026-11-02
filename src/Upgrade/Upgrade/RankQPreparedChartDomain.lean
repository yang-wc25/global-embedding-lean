import Upgrade.CompactRankQSchurPreparation
import Upgrade.IncidencePairChartAvoidance

/-!
# The actual two-chart domain of a fixed prepared rank-q neighborhood

Only the parameter radius varies. The source region is the same one that
was chosen with auxiliary weights before submitting the finite waves.
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

/-- Coordinate domain formed by the actual product partial homeomorphism. -/
def RankQSchurPreparedNeighborhood.coordinateDomain
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
  {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
  {p : RankQLocalWavePacket F₀ hF₀ x y₀}
  {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} (rho : ℝ) (j : Fin A.count) : Set (ProbeParameters r × (E × E)) :=
  (actualPairChart (P := ProbeParameters r) A i j).target ∩ (actualPairChart (P := ProbeParameters r) A i j).symm ⁻¹'
    (Metric.ball 0 rho ×ˢ prep.neighborhood)

theorem RankQSchurPreparedNeighborhood.coordinateDomain_open
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
  {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
  {p : RankQLocalWavePacket F₀ hF₀ x y₀}
  {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} (rho : ℝ) (j : Fin A.count) :
    IsOpen (prep.coordinateDomain (r := r) rho j) :=
  (actualPairChart (P := ProbeParameters r) A i j).symm.isOpen_inter_preimage
    (Metric.isOpen_ball.prod prep.neighborhood_open)

theorem RankQSchurPreparedNeighborhood.mem_coordinateDomain_iff
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
  {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
  {p : RankQLocalWavePacket F₀ hF₀ x y₀}
  {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} (rho : ℝ) (j : Fin A.count) (w : ProbeParameters r × (E × E)) :
    w ∈ prep.coordinateDomain rho j ↔
      ‖w.1‖ < rho ∧ w.2.1 ∈ (A.chart i).target ∧ w.2.2 ∈ (A.chart j).target ∧
        ((A.chart i).symm w.2.1, (A.chart j).symm w.2.2) ∈ prep.neighborhood := by
  change ((w.1 ∈ (univ : Set (ProbeParameters r)) ∧
      w.2.1 ∈ (A.chart i).target ∧ w.2.2 ∈ (A.chart j).target) ∧
      w.1 ∈ Metric.ball 0 rho ∧
      ((A.chart i).symm w.2.1, (A.chart j).symm w.2.2) ∈ prep.neighborhood) ↔ _
  simp only [mem_univ, true_and, Metric.mem_ball, dist_zero_right]
  tauto

theorem RankQSchurPreparedNeighborhood.actual_point_mem_coordinateDomain
    {A : BufferedAtlas M E} {hA : IsSmoothBufferedAtlas A}
  {F₀ : M → V} {hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀} {x y₀ : M}
  {p : RankQLocalWavePacket F₀ hF₀ x y₀}
  {i : Fin A.count} {hx : x ∈ interior (A.support i)}
    (prep : RankQSchurPreparedNeighborhood A hA p i hx)
    {r : ℕ} (rho : ℝ) (j : Fin A.count) (u : ProbeParameters r)
    (hu : ‖u‖ < rho) (zy : M × M) (hzy : zy ∈ prep.neighborhood)
    (hy : zy.2 ∈ (A.chart j).source) :
    (u,A.chart i zy.1,A.chart j zy.2) ∈ prep.coordinateDomain rho j := by
  have hz := hA.support_subset i
    (interior_subset (prep.principal.support zy (prep.subset_principal hzy)))
  apply (prep.mem_coordinateDomain_iff rho j _).mpr
  refine ⟨hu, (A.chart i).map_source hz, (A.chart j).map_source hy, ?_⟩
  simpa only [(A.chart i).left_inv hz, (A.chart j).left_inv hy] using hzy

#print axioms RankQSchurPreparedNeighborhood.coordinateDomain_open
end GlobalEmbedding.Upgrade
