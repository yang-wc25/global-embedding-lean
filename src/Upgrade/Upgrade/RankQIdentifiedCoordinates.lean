import Upgrade.RankQActualSecondForm
import Upgrade.SupportedIdentifiedCoordinates

/-!
# Actual identified probe forms in the fixed rank-q Schur chart

The shared coordinate expression is the same one used by supported incidence:
project the actual identified true form to the original normal fiber at the
reference point, after the actual source-frame transport. On the genuine
projection-gap neighborhood the fixed normal projection is a proved
bijection. It is composed with the provider's actual normal identification;
no arbitrary or assumed normal-frame equivalence is inserted.
-/

noncomputable section
open Manifold Module
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper Paper.SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The fixed projection is the actual equivalence proved by the normal
projection gap, composed with the same probe identification. -/
theorem projectedIdentifiedTrueForm_eq_actualRepresentative
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (e : E ≃L[ℝ] E) :
    projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap =
      rankQActualRepresentative F₀ F hF x z e.toLinearEquiv
        ((Q z).toLinearEquiv.trans
          (fixedNormalCoordinateEquiv F₀ himm x z hgap).toLinearEquiv) := by
  apply ContinuousLinearMap.ext
  intro q
  change (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto
      ((Q z) (trueSecondForm F hF z (symmetricSquareLinearMap e.toLinearMap q)) : V) =
    (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto
      ((Q z) (trueSecondForm F hF z
        ((saturationSymmetricSquareEquiv e.toLinearEquiv).toLinearMap q)) : V)
  rw [saturationSymmetricSquareEquiv_toLinearMap]

/-- Rank of the coordinate expression is rank of the actual new true form.
This uses the genuine source and normal equivalences already constructed. -/
theorem projectedIdentifiedTrueForm_finrank_range
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (e : E ≃L[ℝ] E) :
    finrank ℝ (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap).range =
      finrank ℝ (trueSecondForm F hF z).range := by
  rw [projectedIdentifiedTrueForm_eq_actualRepresentative F₀ F hF himm Q x z hgap e]
  exact rankQActualRepresentative_finrank_range F₀ F hF x z e.toLinearEquiv
    ((Q z).toLinearEquiv.trans (fixedNormalCoordinateEquiv F₀ himm x z hgap).toLinearEquiv)

/-- The actual Schur equation detects exactly the rank-q stratum of the
actual probe slice, on the protected actual block and normal neighborhoods. -/
theorem projectedIdentifiedTrueForm_schur_zero_iff
    (F₀ F : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (e : E ≃L[ℝ] E)
    (hrank : finrank ℝ (trueSecondForm F₀ hF₀ x).range = n * (n - 1) / 2)
    (hA : (rankQBlockA (rankQActualReference F₀ hF₀ x)
      (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap)).IsInvertible) :
    rankQSchur (rankQActualReference F₀ hF₀ x)
      (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap) = 0 ↔
      finrank ℝ (trueSecondForm F hF z).range = n * (n - 1) / 2 := by
  rw [rankQSchur_eq_zero_iff_rank _ _ hA,
    projectedIdentifiedTrueForm_finrank_range F₀ F hF himm Q x z hgap e]
  change finrank ℝ (trueSecondForm F hF z).range =
    finrank ℝ (trueSecondForm F₀ hF₀ x).range ↔ _
  rw [hrank]

end GlobalEmbedding.Upgrade
