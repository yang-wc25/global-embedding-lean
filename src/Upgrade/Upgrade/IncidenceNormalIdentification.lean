import Upgrade.ProbeInterface

/-!
# Quantitative comparison for the actual identified second form

These geometric identities consume a normal identification but do not
construct the polar identification owned by the upstream probes task. They
make its precise zeroth-order obligation visible: map closeness must be
combined with closeness of the chosen identification. Orthogonality alone
only gives the operator bound one.
-/

noncomputable section
open Manifold
open scoped ContDiff

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

/-- The literal true second form included in the ambient Euclidean target. -/
def incidenceAmbientTrueSecondForm (F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (x : M) : SymmetricSquare E →L[ℝ] V :=
  (normalSpace (I := IM) F x).subtypeL.comp
    (LinearMap.toContinuousLinearMap
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F x from trueSecondForm F hF x))

/-- Orthogonality gives a uniform norm bound for the actual ambient operator,
but does not assert its closeness to the old normal projection. -/
theorem normalIdentificationOperator_norm_le_one
    (F₀ F : M → V)
    (Q : ∀ x, normalSpace (I := IM) F x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x) (x : M) :
    ‖normalIdentificationOperator (n := n) F₀ F Q x‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro v
  change ‖(Q x) ((normalSpace (I := IM) F x).orthogonalProjectionOnto v)‖ ≤ 1 * ‖v‖
  rw [(Q x).norm_map, one_mul]
  exact (normalSpace (I := IM) F x).norm_orthogonalProjectionOnto_apply_le v

/-- The identified form is exactly the actual ambient form followed by the
same normal-identification operator. -/
theorem identifiedTrueSecondForm_eq_normalIdentification_comp
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ x, normalSpace (I := IM) F x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x) (x : M) :
    identifiedTrueSecondForm (n := n) F₀ F hF Q x =
      (normalIdentificationOperator (n := n) F₀ F Q x).comp
        (incidenceAmbientTrueSecondForm F hF x) := by
  apply ContinuousLinearMap.ext
  intro q
  change (Q x (trueSecondForm F hF x q) : V) =
    (Q x ((normalSpace (I := IM) F x).orthogonalProjectionOnto
      (trueSecondForm F hF x q : V)) : V)
  rw [Submodule.orthogonalProjectionOnto_mem_subspace_eq_self]

section OperatorEstimate
variable {S W : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup W] [NormedSpace ℝ W]

/-- An elementary operator estimate used with the actual normal data below.
The term involving Q-P is essential and is not absorbed into map closeness. -/
theorem incidence_identification_comparison
    (Q P : W →L[ℝ] W) (B B₀ : S →L[ℝ] W)
    (hQ : ‖Q‖ ≤ 1) (hP : P.comp B₀ = B₀) :
    ‖Q.comp B - B₀‖ ≤ ‖B - B₀‖ + ‖Q - P‖ * ‖B₀‖ := by
  have heq : Q.comp B - B₀ = Q.comp (B - B₀) + (Q - P).comp B₀ := by
    rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp, hP]
    abel
  rw [heq]
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right hQ (norm_nonneg _)).trans_eq (one_mul _))
  · exact ContinuousLinearMap.opNorm_comp_le _ _

end OperatorEstimate

/-- A fixed-frame comparison of the SAME true second forms. Actual C² jet
control supplies the first term; the chosen polar identification supplies the
second. The statement imposes no desired incidence rank. -/
theorem identifiedTrueSecondForm_fixed_frame_error
    (F₀ F : M → V) (hF₀ : ContMDiff IM 𝓘(ℝ, V) ∞ F₀)
    (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ x, normalSpace (I := IM) F x ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ x)
    (x : M) (K : SymmetricSquare E →L[ℝ] SymmetricSquare E) :
    ‖(identifiedTrueSecondForm (n := n) F₀ F hF Q x).comp K -
        (incidenceAmbientTrueSecondForm F₀ hF₀ x).comp K‖ ≤
      ‖(incidenceAmbientTrueSecondForm F hF x).comp K -
        (incidenceAmbientTrueSecondForm F₀ hF₀ x).comp K‖ +
      ‖normalIdentificationOperator (n := n) F₀ F Q x -
        (normalSpace (I := IM) F₀ x).starProjection‖ *
        ‖(incidenceAmbientTrueSecondForm F₀ hF₀ x).comp K‖ := by
  rw [identifiedTrueSecondForm_eq_normalIdentification_comp,
    ContinuousLinearMap.comp_assoc]
  apply incidence_identification_comparison _ _ _ _
    (normalIdentificationOperator_norm_le_one F₀ F Q x)
  apply ContinuousLinearMap.ext
  intro q
  exact (normalSpace (I := IM) F₀ x).starProjection_eq_self_iff.mpr
    (trueSecondForm F₀ hF₀ x (K q)).property

end GlobalEmbedding.Upgrade
