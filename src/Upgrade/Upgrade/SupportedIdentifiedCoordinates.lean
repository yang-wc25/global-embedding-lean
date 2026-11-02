import Upgrade.SupportedProbeAtlasTransport
import Upgrade.SupportedNormalCoordinates

/-!
# Actual supported coordinates for an identified probe slice

The new form is defined from `trueSecondForm` of the new slice, the same
orthogonal identification supplied by probes, and the original fixed normal
projection. An arbitrary orthogonal identification is enough for the exact
support predicate, but is NOT assumed close to the identity. Quantitative
closeness to a reference form must be supplied separately by the polar
identification estimates. This distinction is retained in every theorem.
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

/-- Actual identified true-form coefficients in one fixed original normal
target and the specified actual source frame. -/
def projectedIdentifiedTrueForm
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M) (frame : E →L[ℝ] E) :
    SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x :=
  (normalSpace (I := IM) F₀ x).orthogonalProjectionOnto.comp
    (probeTensorInFrame frame (identifiedTrueSecondForm (n := n) F₀ F hF Q z))

/-- On the actual original normal-coordinate neighborhood, the supported
kernel of the identified/framed operator is exactly the ORIGINAL supported
kernel of the new map. No smallness of Q is needed for this identity. -/
theorem projectedIdentifiedTrueForm_supported_iff
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (e : E ≃L[ℝ] E) :
    HasSupportedKernel (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap).toLinearMap ↔
      HasSupportedKernel (trueSecondForm F hF z) := by
  let j : normalSpace (I := IM) F z →L[ℝ] normalSpace (I := IM) F₀ x :=
    (fixedNormalCoordinate (I := IM) F₀ x z).comp (Q z).toContinuousLinearEquiv.toContinuousLinearMap
  have hj : Function.Injective j :=
    (normal_coordinate_injective (normalSpace (I := IM) F₀ x)
      (normalSpace (I := IM) F₀ z) hgap).comp (Q z).injective
  have hdict :
      (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap).toLinearMap =
        j.toLinearMap.comp
          ((show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F z from trueSecondForm F hF z).comp
            (symmetricSquareLinearMap e.toLinearMap)) := by
    apply LinearMap.ext
    intro q
    rfl
  rw [hdict, hasSupportedKernel_postcomp_iff _ _ hj]
  exact hasSupportedKernel_source_coordinates_iff
    (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := IM) F z from trueSecondForm F hF z) e

/-- The exact supported chart zero means supportedness of the actual probe
slice, after its genuine invertible source frame and normal identification. -/
theorem projectedIdentifiedTrueForm_equation_zero_iff
    (F₀ F : M → V) (hF : ContMDiff IM 𝓘(ℝ, V) ∞ F)
    (Q : ∀ z, normalSpace (I := IM) F z ≃ₗᵢ[ℝ] normalSpace (I := IM) F₀ z)
    (x z : M)
    (hgap : ‖(normalSpace (I := IM) F₀ z).starProjection -
      (normalSpace (I := IM) F₀ x).starProjection‖ < 1)
    (e : E ≃L[ℝ] E)
    (B : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x)
    (chart : SupportedLocusLocalEquations
      {C : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x |
        Function.Surjective C ∧ LinearSecondFormPhaseRegular C.toLinearMap}
      {C : SymmetricSquare E →L[ℝ] normalSpace (I := IM) F₀ x |
        HasSupportedKernel C.toLinearMap} B)
    (hdom : projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap ∈ chart.domain) :
    chart.equation (projectedIdentifiedTrueForm F₀ F hF Q x z e.toContinuousLinearMap) = 0 ↔
      HasSupportedKernel (trueSecondForm F hF z) := by
  rw [← chart.mem_locus_iff _ hdom]
  exact projectedIdentifiedTrueForm_supported_iff F₀ F hF Q x z hgap e

section OperatorProjection
variable {P X Y : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [InnerProductSpace ℝ Y]

/-- Native parameter differentiation commutes with the fixed ORIGINAL normal
projection. All dependence of the actual new normal identification remains
inside C before differentiation. -/
theorem fderiv_fixed_normal_projection
    (W : Submodule ℝ Y) [W.HasOrthogonalProjection]
    (C : P → X →L[ℝ] Y) {u : P} (hC : DifferentiableAt ℝ C u) (d : P) :
    fderiv ℝ (fun v ↦ W.orthogonalProjectionOnto.comp (C v)) u d =
      W.orthogonalProjectionOnto.comp (fderiv ℝ C u d) := by
  exact fderiv_fixed_tensor_left_transport C hC W.orthogonalProjectionOnto d

/-- Fixed normal projection does not increase the full operator remainder. -/
theorem fixed_normal_projection_error
    (W : Submodule ℝ Y) [W.HasOrthogonalProjection]
    (C : P → X →L[ℝ] Y) {u : P} (hC : DifferentiableAt ℝ C u)
    (d : P) (a : ℝ) (T : X →L[ℝ] Y) :
    ‖fderiv ℝ (fun v ↦ W.orthogonalProjectionOnto.comp (C v)) u d -
      a • W.orthogonalProjectionOnto.comp T‖ ≤ ‖fderiv ℝ C u d - a • T‖ := by
  rw [fderiv_fixed_normal_projection W C hC d]
  have heq : W.orthogonalProjectionOnto.comp (fderiv ℝ C u d) -
      a • W.orthogonalProjectionOnto.comp T =
        W.orthogonalProjectionOnto.comp (fderiv ℝ C u d - a • T) := by
    ext v
    simp only [ContinuousLinearMap.comp_apply, sub_apply, smul_apply,
      map_sub, map_smul]
  rw [heq]
  calc
    ‖W.orthogonalProjectionOnto.comp (fderiv ℝ C u d - a • T)‖ ≤
        ‖W.orthogonalProjectionOnto‖ * ‖fderiv ℝ C u d - a • T‖ :=
      ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ 1 * ‖fderiv ℝ C u d - a • T‖ :=
      mul_le_mul_of_nonneg_right W.orthogonalProjectionOnto_norm_le (norm_nonneg _)
    _ = _ := one_mul _

end OperatorProjection

#print axioms projectedIdentifiedTrueForm
#print axioms projectedIdentifiedTrueForm_supported_iff
#print axioms projectedIdentifiedTrueForm_equation_zero_iff
#print axioms fderiv_fixed_normal_projection
#print axioms fixed_normal_projection_error

end GlobalEmbedding.Upgrade
