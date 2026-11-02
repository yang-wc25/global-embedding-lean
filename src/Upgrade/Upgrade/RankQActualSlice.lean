import Upgrade.RankQActualIncidence

/-! Exact parameter-slice identity for the actual two-chart Schur incidence.
It preserves both actual global value endpoints and the actual varying
identified second form. -/
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

theorem actualRankQJointIncidence_parameterSlice
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i j : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (sigma a : ℝ)
    (z y : M) (hz : z ∈ (A.chart i).source) (hy : y ∈ (A.chart j).source) :
    (fun u ↦ actualRankQJointIncidence F₀ hF₀ G hG Q A hA i j x hx sigma a
      (u,A.chart i z,A.chart j y)) =
    (fun u ↦ (sigma⁻¹ • rankQSchur (rankQActualReference F₀ hF₀ x)
      (projectedIdentifiedTrueForm F₀ (G u) (hG u) (Q u) x z
        (probeAtlasNormalizedFrame A hA i x hx z)), a⁻¹ • (G u z - G u y))) := by
  funext u
  change (sigma⁻¹ • rankQSchur (rankQActualReference F₀ hF₀ x)
    (projectedIdentifiedTrueForm F₀ (G u) (hG u) (Q u) x ((A.chart i).symm (A.chart i z))
      (probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm (A.chart i z)))),
    a⁻¹ • (G u ((A.chart i).symm (A.chart i z)) - G u ((A.chart j).symm (A.chart j y)))) = _
  rw [(A.chart i).left_inv hz, (A.chart j).left_inv hy]

end GlobalEmbedding.Upgrade
