import Upgrade.SupportedActualProbeCoordinate
import Upgrade.IncidenceNormalIdentification
import Upgrade.CompactFixedAtlasGeometry

/-!
# Actual identified second form equals the identified fixed-coordinate Hessian

The same normal-identification operator already contains the actual new normal
projection. Therefore applying it to the actual coordinate Hessian gives the
identified true second form in the actual source frame. This exact identity
is what permits joint smoothness to follow from the full original probes
conclusion; a separate smooth second-form surrogate is never introduced.
-/

noncomputable section
open Bundle Manifold Set Module
open scoped ContDiff Topology
namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper GlobalEmbedding.Offline
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

omit [IsManifold IM ∞ M] [BoundarylessManifold IM M] in
theorem normalIdentificationOperator_comp_normalProjection
    (F₀ F : M → V)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    (normalIdentificationOperator (n := n) F₀ F Q z).comp
      (normalSpace (I := IM) F z).starProjection =
        normalIdentificationOperator (n := n) F₀ F Q z := by
  apply ContinuousLinearMap.ext
  intro v
  change (Q z ((normalSpace (I := IM) F z).orthogonalProjectionOnto
      ((normalSpace (I := IM) F z).orthogonalProjectionOnto v : V)) : V) =
    (Q z ((normalSpace (I := IM) F z).orthogonalProjectionOnto v) : V)
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

/-- The literal identified true form in the actual atlas inverse frame is
the same normal-identification operator applied to the actual slice Hessian. -/
theorem identifiedTrueSecondForm_in_atlas_eq_identified_hessian
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (z : M) (hz : z ∈ (A.chart i).source) :
    probeTensorInFrame (probeAtlasFrame A i z) (identifiedTrueSecondForm (n := n) F₀ F hF Q z) =
      (normalIdentificationOperator (n := n) F₀ F Q z).comp (probeAtlasSecondJet A F i z) := by
  have htrue : probeAtlasProjectedSecondForm A F i z =
      probeTensorInFrame (probeAtlasFrame A i z) (incidenceAmbientTrueSecondForm F hF z) := by
    rw [probeAtlasProjectedSecondForm_eq_trueSecondForm A hA F hF i z hz]
    apply ContinuousLinearMap.ext
    intro q
    rfl
  calc
    _ = (normalIdentificationOperator (n := n) F₀ F Q z).comp
        (probeAtlasProjectedSecondForm A F i z) := by
      rw [htrue, identifiedTrueSecondForm_eq_normalIdentification_comp]
      apply ContinuousLinearMap.ext
      intro q
      rfl
    _ = _ := by
      have hproj : (probeAtlasFirstJet A F i z).rangeᗮ.starProjection =
          (normalSpace (I := IM) F z).starProjection := by
        congr 1
        exact (normalSpace_eq_probeAtlasFirstJet_range A hA F hF i z hz).symm
      unfold probeAtlasProjectedSecondForm
      rw [hproj, ← ContinuousLinearMap.comp_assoc,
        normalIdentificationOperator_comp_normalProjection]

/-- Exact fixed-normal normalized-coordinate formula for the actual probe
family, at an actual atlas target point. All parameter dependence is inside
the true slice Hessian and the actual identification operator. -/
theorem actualSupportedProbeCoordinate_eq_identified_hessian
    {P : Type*} (F₀ : M → V) (G : P → M → V)
    (hG : ∀ u, ContMDiff IM 𝓘(ℝ, V) ∞ (G u))
    (Q : ∀ u z, normalSpace (I := IM) (G u) z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A) (i : Fin A.count)
    (x : M) (hx : x ∈ (A.chart i).source) (w : P × E)
    (hw : w.2 ∈ (A.chart i).target) :
    actualSupportedProbeCoordinate F₀ G hG Q A hA i x hx w =
      (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
        (((normalIdentificationOperator (n := n) F₀ (G w.1) (Q w.1) ((A.chart i).symm w.2)).comp
          (coordinateHessianJet (fun v ↦ G w.1 ((A.chart i).symm v)) w.2)).comp
            (probeAtlasNormalizationSquare A hA i x hx)) := by
  unfold actualSupportedProbeCoordinate projectedIdentifiedTrueForm
  rw [probeTensorInFrame_normalized,
    identifiedTrueSecondForm_in_atlas_eq_identified_hessian F₀ (G w.1) (hG w.1) (Q w.1)
      A hA i ((A.chart i).symm w.2) ((A.chart i).map_target hw)]
  congr 3
  change coordinateHessianJet (G w.1 ∘ (A.chart i).symm)
      (A.chart i ((A.chart i).symm w.2)) = _
  rw [(A.chart i).right_inv hw]
  rfl

#print axioms normalIdentificationOperator_comp_normalProjection
#print axioms identifiedTrueSecondForm_in_atlas_eq_identified_hessian
#print axioms actualSupportedProbeCoordinate_eq_identified_hessian

end GlobalEmbedding.Upgrade
