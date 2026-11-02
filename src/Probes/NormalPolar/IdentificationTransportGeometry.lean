import Upgrade.IncidenceNormalIdentification
import Mathlib.Analysis.InnerProductSpace.Adjoint

/-!
# The actual change of normal identification for the same map

Two normal identifications of the same actual map differ by an isometry of
the old normal space. Its ambient operator is the new Qop followed by the
adjoint of the old Qop. The true identified second form transforms by this
same operator, including after the original source-frame transport.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Paper GlobalEmbedding.Upgrade SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) M]

local notation "IM" => 𝓘(ℝ, EuclideanSpace ℝ (Fin n))
local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- The adjoint of the genuine ambient identification is the ambient
operator of the inverse actual normal isometry. -/
theorem normalIdentificationOperator_adjoint
    (F₀ F : M → V)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    (normalIdentificationOperator (n := n) F₀ F Q z).adjoint =
      normalIdentificationOperator (n := n) F F₀ (fun x ↦ (Q x).symm) z := by
  simp only [normalIdentificationOperator, ContinuousLinearMap.adjoint_comp,
    Submodule.adjoint_subtypeL, Submodule.adjoint_orthogonalProjectionOnto]
  rw [LinearIsometryEquiv.adjoint_eq_symm]
  rfl

/-- The ambient partial isometry times its adjoint is precisely the old
true normal projection, including when that normal space is zero. -/
theorem normalIdentificationOperator_comp_adjoint
    (F₀ F : M → V)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    (normalIdentificationOperator (n := n) F₀ F Q z).comp
        (normalIdentificationOperator (n := n) F₀ F Q z).adjoint =
      (normalSpace (I := IM) F₀ z).starProjection := by
  rw [normalIdentificationOperator_adjoint]
  apply ContinuousLinearMap.ext
  intro v
  change (Q z ((normalSpace (I := IM) F z).orthogonalProjectionOnto
      ((Q z).symm ((normalSpace (I := IM) F₀ z).orthogonalProjectionOnto v) : V)) : V) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.apply_symm_apply]
  rfl

theorem normalIdentificationOperator_adjoint_comp
    (F₀ F : M → V)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    (normalIdentificationOperator (n := n) F₀ F Q z).adjoint.comp
        (normalIdentificationOperator (n := n) F₀ F Q z) =
      (normalSpace (I := IM) F z).starProjection := by
  simpa only [normalIdentificationOperator_adjoint, LinearIsometryEquiv.symm_symm] using
    normalIdentificationOperator_comp_adjoint F F₀ (fun x ↦ (Q x).symm) z

/-- The actual old-normal automorphism taking the old Q image to the new
Q image. Both identifications have the same actual domain normal space. -/
def normalIdentificationGauge
    (F₀ F : M → V)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) : normalSpace (I := IM) F₀ z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z :=
  (Qold z).symm.trans (Qnew z)

/-- Use the original ambient normal-identification definition on the old
normal bundle itself. No independent gauge operator is supplied. -/
def normalIdentificationGaugeOperator
    (F₀ F : M → V)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) : V →L[ℝ] V :=
  normalIdentificationOperator (n := n) F₀ F₀
    (normalIdentificationGauge F₀ F Qold Qnew) z

theorem normalIdentificationGaugeOperator_eq_comp_adjoint
    (F₀ F : M → V)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    normalIdentificationGaugeOperator F₀ F Qold Qnew z =
      (normalIdentificationOperator (n := n) F₀ F Qnew z).comp
        (normalIdentificationOperator (n := n) F₀ F Qold z).adjoint := by
  rw [normalIdentificationOperator_adjoint]
  apply ContinuousLinearMap.ext
  intro v
  change (Qnew z ((Qold z).symm ((normalSpace (I := IM) F₀ z).orthogonalProjectionOnto v)) : V) =
    (Qnew z ((normalSpace (I := IM) F z).orthogonalProjectionOnto
      ((Qold z).symm ((normalSpace (I := IM) F₀ z).orthogonalProjectionOnto v) : V)) : V)
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

theorem normalIdentificationGaugeOperator_comp_old
    (F₀ F : M → V)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    (normalIdentificationGaugeOperator F₀ F Qold Qnew z).comp
        (normalIdentificationOperator (n := n) F₀ F Qold z) =
      normalIdentificationOperator (n := n) F₀ F Qnew z := by
  apply ContinuousLinearMap.ext
  intro v
  change (Qnew z ((Qold z).symm ((normalSpace (I := IM) F₀ z).orthogonalProjectionOnto
      (Qold z ((normalSpace (I := IM) F z).orthogonalProjectionOnto v) : V))) : V) = _
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self,
    LinearIsometryEquiv.symm_apply_apply]
  rfl

theorem normalIdentificationGaugeOperator_norm_le_one
    (F₀ F : M → V)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) : ‖normalIdentificationGaugeOperator F₀ F Qold Qnew z‖ ≤ 1 :=
  normalIdentificationOperator_norm_le_one F₀ F₀
    (normalIdentificationGauge F₀ F Qold Qnew) z

/-- Gauge closeness is bounded by the difference of the two actual Qops.
It is not inferred from orthogonality alone. -/
theorem normalIdentificationGaugeOperator_sub_projection_le
    (F₀ F : M → V)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    ‖normalIdentificationGaugeOperator F₀ F Qold Qnew z -
        (normalSpace (I := IM) F₀ z).starProjection‖ ≤
      ‖normalIdentificationOperator (n := n) F₀ F Qnew z -
        normalIdentificationOperator (n := n) F₀ F Qold z‖ := by
  rw [normalIdentificationGaugeOperator_eq_comp_adjoint,
    ← normalIdentificationOperator_comp_adjoint F₀ F Qold z,
    ← ContinuousLinearMap.sub_comp]
  apply (ContinuousLinearMap.opNorm_comp_le _ _).trans
  have h := normalIdentificationOperator_norm_le_one F₀ F Qold z
  simpa only [LinearIsometryEquiv.norm_map, mul_one] using
    mul_le_mul_of_nonneg_left h
      (norm_nonneg (normalIdentificationOperator (n := n) F₀ F Qnew z -
        normalIdentificationOperator (n := n) F₀ F Qold z))

/-- The true identified second form for the new choice is the actual gauge
applied to the old identified true form. The map F is unchanged. -/
theorem identifiedTrueSecondForm_eq_gauge_comp
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) :
    identifiedTrueSecondForm (n := n) F₀ F hF Qnew z =
      (normalIdentificationGaugeOperator F₀ F Qold Qnew z).comp
        (identifiedTrueSecondForm (n := n) F₀ F hF Qold z) := by
  rw [identifiedTrueSecondForm_eq_normalIdentification_comp F₀ F hF Qnew,
    identifiedTrueSecondForm_eq_normalIdentification_comp F₀ F hF Qold,
    ← ContinuousLinearMap.comp_assoc, normalIdentificationGaugeOperator_comp_old]

/-- The same change of identification commutes with the original fixed
source frame; no replacement of the atlas or its supports is performed. -/
theorem framed_identifiedTrueSecondForm_eq_gauge_comp
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Qold Qnew : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (z : M) (frame : E →L[ℝ] E) :
    probeTensorInFrame frame (identifiedTrueSecondForm (n := n) F₀ F hF Qnew z) =
      (normalIdentificationGaugeOperator F₀ F Qold Qnew z).comp
        (probeTensorInFrame frame (identifiedTrueSecondForm (n := n) F₀ F hF Qold z)) := by
  rw [identifiedTrueSecondForm_eq_gauge_comp F₀ F hF Qold Qnew]
  exact ContinuousLinearMap.comp_assoc _ _ _

end GlobalEmbedding.NormalPolar
