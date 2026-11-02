import Upgrade.SupportedIdentifiedCoordinates

/-!
# One literal supported-incidence coordinate map for an actual probe family

The source argument is in the selected actual atlas chart. The family enters
only through its actual smooth slice and its actual normal identification.
The fixed normalization is constructed from that atlas chart, so it is the
identity at the selected center and retains every source-frame variation.
This module constructs no probes and assumes no incidence rank.
-/

noncomputable section
open Bundle Manifold Set Module
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The actual supported-coordinate field used in the n≥4 operation. P is
the finite parameter space after the standard finite-label reindexing. -/
def actualSupportedProbeCoordinate
    {P : Type*} (F₀ : M → V) (G : P → M → V)
    (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (w : P × E) :
    SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
  projectedIdentifiedTrueForm F₀ (G w.1) (hG w.1) (Q w.1) x ((A.chart i).symm w.2)
    (probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm w.2))

/-- The actual coordinate field's supported predicate equals supportedness
of the original new slice, at the actual chart inverse point. The only normal
condition is the proved original fixed-coordinate projection margin. -/
theorem actualSupportedProbeCoordinate_supported_iff
    {P : Type*} (F₀ : M → V) (G : P → M → V)
    (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (w : P × E)
    (hw : w.2 ∈ (A.chart i).target)
    (hgap : ‖(normalSpace (I := IM) F₀ ((A.chart i).symm w.2)).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1) :
    HasSupportedKernel (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx w).toLinearMap ↔
      HasSupportedKernel (trueSecondForm (G w.1) (hG w.1) ((A.chart i).symm w.2)) := by
  let e := probeAtlasNormalizedFrameEquiv A hA i x hx ((A.chart i).symm w.2)
    ((A.chart i).map_target hw)
  have he : e.toContinuousLinearMap =
      probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm w.2) :=
    probeAtlasNormalizedFrameEquiv_toContinuousLinearMap A hA i x hx
      ((A.chart i).symm w.2) ((A.chart i).map_target hw)
  have h := projectedIdentifiedTrueForm_supported_iff F₀ (G w.1) (hG w.1) (Q w.1)
    x ((A.chart i).symm w.2) hgap e
  rw [he] at h
  exact h

/-- Zeroes of the actual supported equation are exactly the actual supported
kernels of the new slice. This is the literal incidence consumed by avoidance. -/
theorem actualSupportedProbeCoordinate_equation_zero_iff
    {P : Type*} (F₀ : M → V) (G : P → M → V)
    (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (w : P × E)
    (hw : w.2 ∈ (A.chart i).target)
    (hgap : ‖(normalSpace (I := IM) F₀ ((A.chart i).symm w.2)).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (chart : SupportedLocusLocalEquations
      {C : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x |
        Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
      {C : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x |
        HasSupportedKernel C.toLinearMap} B)
    (hdom : actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx w ∈ chart.domain) :
    chart.equation (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx w) = 0 ↔
      HasSupportedKernel (trueSecondForm (G w.1) (hG w.1) ((A.chart i).symm w.2)) := by
  rw [← chart.mem_locus_iff _ hdom]
  exact actualSupportedProbeCoordinate_supported_iff F₀ G hG Q A hA i x hx w hw hgap

#print axioms actualSupportedProbeCoordinate
#print axioms actualSupportedProbeCoordinate_supported_iff
#print axioms actualSupportedProbeCoordinate_equation_zero_iff

end GlobalEmbedding.Upgrade
