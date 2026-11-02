import Round2.MetricLeftInverse
import Upgrade.SupportedIdentifiedHessian
import Upgrade.SupportedNormalCoordinates

/-!
# The actual normal/tangent splitting for the chosen probe identification

The right inverse below is constructed from the SAME chosen orthogonal normal
identification and the already proved fixed-normal coordinate equivalence.
Together with the actual Gram tangent inverse it splits the ambient identity.
No derivative or norm bound for the normal-coordinate right inverse is used.
-/

noncomputable section
open Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open Paper

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]
local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Actual chosen normal identification followed by the fixed original normal
coordinate projection. -/
def gaugeActualNormalOperator (F₀ F : M → V)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M) : V →L[ℝ] normalSpace (I := IM) F₀ x :=
  (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
    (normalIdentificationOperator (n := n) F₀ F Q z)

/-- Pointwise right inverse on the actual new normal image. Its derivative is
never taken; it factors the gauge derivative at a single incidence zero. -/
def gaugeActualNormalRightInverse (F₀ F : M → V)
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1) :
    normalSpace (I := IM) F₀ x →L[ℝ] V :=
  (normalSpace (I := IM) F z).subtypeL.comp
    ((Q z).symm.toContinuousLinearEquiv.toContinuousLinearMap.comp
      (fixedNormalCoordinateEquiv F₀ himm₀ x z hgap).symm.toContinuousLinearMap)

/-- The actual normal right inverse recovers exactly the new normal
projection, not the ambient identity. -/
theorem gaugeActualNormalRightInverse_comp (F₀ F : M → V)
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1) :
    (gaugeActualNormalRightInverse F₀ F himm₀ Q x z hgap).comp
      (gaugeActualNormalOperator F₀ F Q x z) =
      (normalSpace (I := IM) F z).starProjection := by
  apply ContinuousLinearMap.ext
  intro v
  change ((Q z).symm ((fixedNormalCoordinateEquiv F₀ himm₀ x z hgap).symm
    ((fixedNormalCoordinateEquiv F₀ himm₀ x z hgap)
      (Q z ((normalSpace (I := IM) F z).orthogonalProjectionOnto v)))) : V) = _
  rw [ContinuousLinearEquiv.symm_apply_apply, LinearIsometryEquiv.symm_apply_apply]
  rfl

/-- Norm one follows from actual orthogonality and the fixed normal
projection. It does not imply a bound for any spatial derivative. -/
theorem gaugeActualNormalOperator_norm_le_one (F₀ F : M → V)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M) : ‖gaugeActualNormalOperator F₀ F Q x z‖ ≤ 1 := by
  exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
    ((mul_le_mul (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto_norm_le
      (normalIdentificationOperator_norm_le_one F₀ F Q z) (by positivity) (by norm_num))
        |>.trans_eq (one_mul 1))

/-- The normal projection kills the actual fixed-atlas first jet. -/
theorem actualNormalProjection_probeAtlasFirstJet_zero
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (i : Fin A.count) (z : M) (hz : z ∈ (A.chart i).source) (v : E) :
    (normalSpace (I := IM) F z).orthogonalProjectionOnto
      (probeAtlasFirstJet A F i z v) = 0 := by
  apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
  rw [normalSpace_eq_probeAtlasFirstJet_range A hA F hF i z hz]
  exact Submodule.le_orthogonal_orthogonal _ ⟨v, rfl⟩

/-- The SAME actual normal coordinate operator kills the SAME actual tangent
jet. This is the identity differentiated in the cancellation lemma. -/
theorem gaugeActualNormalOperator_comp_firstJet_zero
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (i : Fin A.count) (x z : M) (hz : z ∈ (A.chart i).source) :
    (gaugeActualNormalOperator F₀ F Q x z).comp (probeAtlasFirstJet A F i z) = 0 := by
  apply ContinuousLinearMap.ext
  intro v
  change (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto
    (Q z ((normalSpace (I := IM) F z).orthogonalProjectionOnto
      (probeAtlasFirstJet A F i z v)) : V) = 0
  rw [actualNormalProjection_probeAtlasFirstJet_zero A hA F hF i z hz v, map_zero]
  exact map_zero _

/-- The exact normal/tangent splitting of the ambient identity in the actual
source chart. In particular no source frame variation is omitted. -/
theorem gaugeActualNormal_tangent_split
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (himm₀ : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F₀ z))
    (himm : ∀ z, Function.Injective (mfderiv IM 𝓘(ℝ, V) F z))
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (i : Fin A.count) (x z : M) (hz : z ∈ (A.chart i).source)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1) :
    (gaugeActualNormalRightInverse F₀ F himm₀ Q x z hgap).comp
      (gaugeActualNormalOperator F₀ F Q x z) +
      (probeAtlasFirstJet A F i z).comp (probeAtlasTangentLeftInverse A F i z) =
      ContinuousLinearMap.id ℝ V := by
  rw [gaugeActualNormalRightInverse_comp,
    (probeAtlasTangentLeftInverse_identities A hA F hF i z hz (himm z)).2,
    normalSpace_eq_probeAtlasFirstJet_range A hA F hF i z hz,
    Submodule.starProjection_orthogonal]
  abel

#print axioms gaugeActualNormalRightInverse_comp
#print axioms gaugeActualNormalOperator_norm_le_one
#print axioms gaugeActualNormalOperator_comp_firstJet_zero
#print axioms gaugeActualNormal_tangent_split

end GlobalEmbedding.Upgrade
