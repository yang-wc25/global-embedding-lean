import NormalPolar.ConstructionPolarAlgebra

/-!
An actual orthogonal identification of two close normal subspaces. The map is
the restriction of the explicit ambient polar operator, and the final theorem
identifies its ambient extension exactly with the operator used in all gap
and response estimates. Zero-dimensional subspaces are included.
-/

noncomputable section
namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

theorem actualAmbientPolar_mem (K L : Submodule ℝ V) (v : L) :
    actualAmbientPolar K.starProjection L.starProjection (v : V) ∈ K := by
  apply K.starProjection_eq_self_iff.mp
  have h := congrArg (fun T : V →L[ℝ] V ↦ T (v : V))
    (actualAmbientPolar_intertwine K.starProjection L.starProjection
      K.isIdempotentElem_starProjection L.isIdempotentElem_starProjection)
  simpa only [mul_apply_eq_comp, Submodule.starProjection_mem_subspace_eq_self]
    using h.symm

theorem actualAmbientPolar_adjoint_mem (K L : Submodule ℝ V) (v : K) :
    (actualAmbientPolar K.starProjection L.starProjection).adjoint (v : V) ∈ L := by
  apply L.starProjection_eq_self_iff.mp
  have h := congrArg (fun T : V →L[ℝ] V ↦ T (v : V))
    (actualAmbientPolar_star_intertwine K.starProjection L.starProjection
      (isStarProjection_starProjection (U := K)) (isStarProjection_starProjection (U := L)))
  simpa only [mul_apply_eq_comp, Submodule.starProjection_mem_subspace_eq_self,
    ContinuousLinearMap.star_eq_adjoint] using h

def actualNormalPolarMap (K L : Submodule ℝ V) : L →ₗ[ℝ] K :=
  ((actualAmbientPolar K.starProjection L.starProjection).toLinearMap.comp L.subtype).codRestrict
    K (actualAmbientPolar_mem K L)

@[simp] theorem actualNormalPolarMap_coe (K L : Submodule ℝ V) (v : L) :
    (actualNormalPolarMap K L v : V) =
      actualAmbientPolar K.starProjection L.starProjection (v : V) := rfl

theorem actualNormalPolarMap_norm (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) (v : L) :
    ‖actualNormalPolarMap K L v‖ = ‖v‖ := by
  have h := actualAmbientPolar_star_mul K.starProjection L.starProjection
    (isStarProjection_starProjection (U := K)) (isStarProjection_starProjection (U := L)) hclose
  change (actualAmbientPolar K.starProjection L.starProjection).adjoint.comp
    (actualAmbientPolar K.starProjection L.starProjection) = ContinuousLinearMap.id ℝ V at h
  exact (ContinuousLinearMap.norm_map_iff_adjoint_comp_self _).mpr h (v : V)

def actualNormalPolarIsometry (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) : L →ₗᵢ[ℝ] K where
  toLinearMap := actualNormalPolarMap K L
  norm_map' := actualNormalPolarMap_norm K L hclose

theorem actualNormalPolarMap_surjective (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    Function.Surjective (actualNormalPolarMap K L) := by
  intro v
  refine ⟨⟨(actualAmbientPolar K.starProjection L.starProjection).adjoint v,
    actualAmbientPolar_adjoint_mem K L v⟩, ?_⟩
  apply Subtype.ext
  have h := congrArg (fun T : V →L[ℝ] V ↦ T (v : V))
    (actualAmbientPolar_mul_star K.starProjection L.starProjection
      (isStarProjection_starProjection (U := K)) (isStarProjection_starProjection (U := L)) hclose)
  exact h

/-- The explicitly constructed new-to-old orthogonal normal identification. -/
def actualNormalPolarEquiv (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) : L ≃ₗᵢ[ℝ] K :=
  LinearIsometryEquiv.ofSurjective (actualNormalPolarIsometry K L hclose)
    (actualNormalPolarMap_surjective K L hclose)

@[simp] theorem actualNormalPolarEquiv_coe (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) (v : L) :
    (actualNormalPolarEquiv K L hclose v : V) =
      actualAmbientPolar K.starProjection L.starProjection (v : V) := rfl

/-- The actual ambient operator of this same normal equivalence is exactly
the analytic formula used in the smoothness, derivative, and gap theorems. -/
theorem actualNormalPolarEquiv_operator (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1) :
    K.subtypeL.comp ((actualNormalPolarEquiv K L hclose).toContinuousLinearEquiv.toContinuousLinearMap.comp
      L.orthogonalProjectionOnto) = actualPolarOperator K.starProjection L.starProjection := by
  calc
    _ = actualAmbientPolar K.starProjection L.starProjection * L.starProjection := by
      ext v
      rfl
    _ = actualPolarOperator K.starProjection L.starProjection :=
      actualAmbientPolar_mul_new _ _ L.isIdempotentElem_starProjection

end GlobalEmbedding.NormalPolar
