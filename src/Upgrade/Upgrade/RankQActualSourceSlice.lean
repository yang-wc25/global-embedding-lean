import Upgrade.RankQActualIncidence

/-! Exact first-source slice of the actual two-chart Schur incidence. -/
noncomputable section
open Function Manifold Module
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

theorem actualRankQJointIncidence_sourceSlice
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i j : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (sigma a : ℝ)
    (u : P) (y : M) (hy : y ∈ (A.chart j).source) :
    (fun s ↦ actualRankQJointIncidence F₀ hF₀ G hG Q A hA i j x hx sigma a
      (u,s,A.chart j y)) =
    (fun s ↦ (sigma⁻¹ • rankQSchur (rankQActualReference F₀ hF₀ x)
      (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (u,s)),
      a⁻¹ • (G u ((A.chart i).symm s) - G u y))) := by
  funext s
  change (sigma⁻¹ • rankQSchur (rankQActualReference F₀ hF₀ x)
    (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (u,s)),
    a⁻¹ • (G u ((A.chart i).symm s) - G u ((A.chart j).symm (A.chart j y)))) = _
  rw [(A.chart j).left_inv hy]

end GlobalEmbedding.Upgrade
