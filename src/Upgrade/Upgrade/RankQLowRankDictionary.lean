import Upgrade.RankQActualIncidence

/-!
# The actual protected Schur block excludes smaller ranks

The low-rank coincidence bad set uses rank at most q.  The constructed
invertible q block proves rank at least q for the actual true second form,
so the literal Schur/value zero set is exactly this low-rank bad set.  This
lower bound is derived; no nearby rank hypothesis is added.
-/
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

/-- The actual nearby true form has rank at least the reference rank when
its actual fixed-normal/source Schur block is invertible. -/
theorem projectedIdentifiedTrueForm_reference_rank_le
    (F₀ F : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (e : E ≃L[ℝ] E)
    (hblock : (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap)).IsInvertible) :
    finrank ℝ (trueSecondForm F₀ hF₀ x).range ≤ finrank ℝ (trueSecondForm F hF z).range := by
  have hsplit := rankQSchur_finrank_range (rankQActualReference F₀ hF₀ x)
    (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap) hblock
  rw [projectedIdentifiedTrueForm_finrank_range F₀ F hF himm Q x z hgap e] at hsplit
  change finrank ℝ (trueSecondForm F hF z).range =
    finrank ℝ (trueSecondForm F₀ hF₀ x).range + _ at hsplit
  omega

/-- Exact dictionary for the original low-rank two-point bad set.  The source
points may belong to different connected components and to different charts. -/
theorem actualRankQJointIncidence_zero_iff_rank_le
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (F₀ : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (himm : ∀ z, Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (G : P → M → V) (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (i j : Fin A.count) (x : M) (hx : x ∈ (A.chart i).source)
    (sigma a : ℝ) (hsigma : sigma ≠ 0) (ha : a ≠ 0)
    (w : P × (E × E)) (hw : w.2.1 ∈ (A.chart i).target)
    (hgap : ‖(normalSpace (I := IM) F₀ ((A.chart i).symm w.2.1)).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (hrank : finrank ℝ (trueSecondForm F₀ hF₀ x).range = n * (n - 1) / 2)
    (hblock : (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx (w.1,w.2.1))).IsInvertible) :
    actualRankQJointIncidence F₀ hF₀ G hG Q A hA i j x hx sigma a w = 0 ↔
      finrank ℝ (trueSecondForm (G w.1) (hG w.1) ((A.chart i).symm w.2.1)).range ≤
          n * (n - 1) / 2 ∧
        G w.1 ((A.chart i).symm w.2.1) = G w.1 ((A.chart j).symm w.2.2) := by
  have heq := actualRankQJointIncidence_zero_iff F₀ hF₀ himm G hG Q A hA i j x hx
    sigma a hsigma ha w hw hgap hrank hblock
  let e := probeAtlasNormalizedFrameEquiv A hA i x hx ((A.chart i).symm w.2.1)
    ((A.chart i).map_target hw)
  have he : e.toContinuousLinearMap =
      probeAtlasNormalizedFrame A hA i x hx ((A.chart i).symm w.2.1) :=
    probeAtlasNormalizedFrameEquiv_toContinuousLinearMap A hA i x hx
      ((A.chart i).symm w.2.1) ((A.chart i).map_target hw)
  have hb : (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (projectedIdentifiedTrueForm F₀ (G w.1) (hG w.1) (Q w.1)
        x ((A.chart i).symm w.2.1) e.toContinuousLinearMap)).IsInvertible := by
    rw [he]
    exact hblock
  have hlower := projectedIdentifiedTrueForm_reference_rank_le F₀ (G w.1) hF₀
    (hG w.1) himm (Q w.1) x ((A.chart i).symm w.2.1) hgap e hb
  rw [hrank] at hlower
  rw [heq]
  exact and_congr (⟨Eq.le, fun h ↦ le_antisymm h hlower⟩) Iff.rfl

#print axioms projectedIdentifiedTrueForm_reference_rank_le
#print axioms actualRankQJointIncidence_zero_iff_rank_le
end GlobalEmbedding.Upgrade
