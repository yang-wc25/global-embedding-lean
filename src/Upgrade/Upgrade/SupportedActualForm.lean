import Upgrade.SupportedNormalCoordinates
import GlobalEmbedding.Paper.SymmetricSquareMapIdentity

/-!
# The actual smooth supported-incidence coordinate field

The coordinate operator below is constructed from the true second fundamental
form, the actual inverse tangent trivialization, and a fixed original normal
projection. The support predicate is proved equivalent to the original one
on a genuine neighborhood, and the coordinate operator equals the original
second form at the base point. No replacement field is assumed.
-/

noncomputable section
open Bundle Manifold Set Module
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade
open GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] {N : ℕ}

/-- Actual supported coordinates exist and are smooth. Their support zeros
refer to the original true form on its actual tangent and normal fibers.
Both the varying source frame and the normal-coordinate lower bound survive
in the output; no global normal trivialization is required. -/
theorem exists_actual_supported_coordinate_field
    (F : M → EuclideanSpace ℝ (Fin N))
    (hF : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ F)
    (himm : ∀ z, Function.Injective (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F z))
    (x : M) :
    ∃ (U : Set M) (C : M → SymmetricSquare E →L[ℝ] normalSpace (I := I) F x),
      IsOpen U ∧ x ∈ U ∧ U ⊆ (chartAt H x).source ∧
      ContMDiffOn I 𝓘(ℝ, SymmetricSquare E →L[ℝ] normalSpace (I := I) F x) ∞ C U ∧
      C x = LinearMap.toContinuousLinearMap
        (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) F x from trueSecondForm F hF x) ∧
      (∀ z q, C z q = (normalSpace (I := I) F x).orthogonalProjectionOnto
        (trueSecondForm F hF z
          (symmetricSquareLinearMap
            ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap q) :
              EuclideanSpace ℝ (Fin N))) ∧
      ∀ z ∈ U,
        (HasSupportedKernel (C z).toLinearMap ↔ HasSupportedKernel (trueSecondForm F hF z)) ∧
        Function.Injective (fixedNormalCoordinate (I := I) F x z) ∧
        ∀ v : normalSpace (I := I) F z,
          (1 / 2 : ℝ) * ‖v‖ ≤ ‖fixedNormalCoordinate (I := I) F x z v‖ := by
  obtain ⟨U, hU, hx, hUc, hnormal⟩ :=
    exists_fixed_normal_coordinate_neighborhood F hF himm x
  obtain ⟨A, hA, hAeq⟩ := upgrade_exists_true_form_coefficients F hF himm x
    (LinearMap.id : SymmetricSquare E →ₗ[ℝ] SymmetricSquare E)
  let C (z : M) : SymmetricSquare E →L[ℝ] normalSpace (I := I) F x :=
    (normalSpace (I := I) F x).orthogonalProjectionOnto.comp (A z)
  have hCeq (z : M) (q : SymmetricSquare E) :
      C z q = (normalSpace (I := I) F x).orthogonalProjectionOnto
        (trueSecondForm F hF z
          (symmetricSquareLinearMap
            ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap q) :
              EuclideanSpace ℝ (Fin N)) := by
    change (normalSpace (I := I) F x).orthogonalProjectionOnto (A z q) = _
    rw [hAeq]
    rfl
  refine ⟨U, C, hU, hx, hUc, ?_, ?_, hCeq, ?_⟩
  · exact (contMDiffOn_const.clm_comp hA).mono hUc
  · apply ContinuousLinearMap.ext
    intro q
    rw [hCeq]
    have hframe : (trivializationAt E (TangentSpace I) x).symmL ℝ x =
        ContinuousLinearMap.id ℝ E := by
      rw [TangentBundle.symmL_trivializationAt (mem_chart_source H x),
        mfderivWithin_range_extChartAt_symm]
      rfl
    change (normalSpace (I := I) F x).orthogonalProjectionOnto
      ((show SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) F x from trueSecondForm F hF x)
        (symmetricSquareLinearMap
          (show E →ₗ[ℝ] E from ((trivializationAt E (TangentSpace I) x).symmL ℝ x).toLinearMap) q) :
        EuclideanSpace ℝ (Fin N)) = _
    have hid : symmetricSquareLinearMap (ContinuousLinearMap.id ℝ E).toLinearMap =
        symmetricSquareMap (ContinuousLinearMap.id ℝ E) :=
      symmetric_square_linear_map_eq (ContinuousLinearMap.id ℝ E)
    rw [hframe, hid, symmetricSquareMap_id]
    exact (normalSpace (I := I) F x).orthogonalProjectionOnto_mem_subspace_eq_self _
  · intro z hz
    have hz0 : z ∈ (trivializationAt E (TangentSpace I) x).baseSet := hUc hz
    let e : E ≃L[ℝ] E :=
      ((trivializationAt E (TangentSpace I) x).continuousLinearEquivAt ℝ z hz0).symm
    have he : e.toLinearMap =
        ((trivializationAt E (TangentSpace I) x).symmL ℝ z).toLinearMap := by
      exact congrArg ContinuousLinearMap.toLinearMap
        ((trivializationAt E (TangentSpace I) x).symm_continuousLinearEquivAt_eq' hz0)
    have hdict : (C z).toLinearMap =
        (fixedNormalCoordinate (I := I) F x z).toLinearMap.comp
          ((show SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) F z from trueSecondForm F hF z).comp
            (symmetricSquareLinearMap e.toLinearMap)) := by
      apply LinearMap.ext
      intro q
      change C z q = (normalSpace (I := I) F x).orthogonalProjectionOnto
        (trueSecondForm F hF z (symmetricSquareLinearMap e.toLinearMap q) :
          EuclideanSpace ℝ (Fin N))
      rw [he, hCeq]
      rfl
    refine ⟨?_, (hnormal z hz).2.1, (hnormal z hz).2.2⟩
    rw [hdict, hasSupportedKernel_postcomp_iff _ _ (hnormal z hz).2.1]
    exact hasSupportedKernel_source_coordinates_iff
      (show SymmetricSquare E →ₗ[ℝ] normalSpace (I := I) F z from trueSecondForm F hF z) e

#print axioms exists_actual_supported_coordinate_field

end GlobalEmbedding.Upgrade
