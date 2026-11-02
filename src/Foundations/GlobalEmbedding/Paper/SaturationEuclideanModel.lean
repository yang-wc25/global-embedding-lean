import GlobalEmbedding.Paper.SymmetricSquareLinearEquivalence
import GlobalEmbedding.Paper.SymmetricSquareOperatorSupport
import GlobalEmbedding.Paper.QuadraticSpaceDimension
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Faithful Euclidean quadratic model of the original norm-only source

Source: original `prop:saturation`, lines 948–995; revised 1779–1843.
DAG: saturation-euclidean-quadratic-model. Exclusive W1 scope.
The original V has no chosen inner product. Its SAME symmetric quotient is
transported algebraically using the already canonical quotient equivalence.
-/

noncomputable section
open scoped TensorProduct
namespace GlobalEmbedding.Paper

section Algebraic
variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- Algebraic part of the existing canonical quotient equivalence. The module
topologies are used only inside the existing existence proof, not on outer V.
Source: coordinate transport in the original saturation argument. -/
def saturationSymmetricSquareEquiv (e : V ≃ₗ[ℝ] W) :
    SymmetricSquare V ≃ₗ[ℝ] SymmetricSquare W := by
  letI := symmetricSquareModuleTopology V
  letI := symmetricSquareModuleTopology W
  exact (Classical.choose (exists_symmetric_square_linear_equivalence e)).toLinearEquiv

/-- Product rule inherited from the canonical equivalence, without new descent.
Source: the SAME binary quotient under a coordinate change. -/
theorem saturationSymmetricSquareEquiv_product (e : V ≃ₗ[ℝ] W) (v w : V) :
    saturationSymmetricSquareEquiv e (symmetricSquareProduct V v w) =
      symmetricSquareProduct W (e v) (e w) := by
  let := symmetricSquareModuleTopology V
  let := symmetricSquareModuleTopology W
  exact Classical.choose_spec (exists_symmetric_square_linear_equivalence e) v w

/-- The inherited algebraic equivalence is literally the original functor.
Source: exact coordinate identification, not a replacement quotient. -/
theorem saturationSymmetricSquareEquiv_toLinearMap (e : V ≃ₗ[ℝ] W) :
    (saturationSymmetricSquareEquiv e).toLinearMap =
      symmetricSquareLinearMap e.toLinearMap := by
  apply (symmetricSquareRelations V).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change saturationSymmetricSquareEquiv e (symmetricSquareProduct V v w) =
    symmetricSquareLinearMap e.toLinearMap (symmetricSquareProduct V v w)
  rw [saturationSymmetricSquareEquiv_product]
  exact (symmetricBilinearDescend_product
    (((symmetricSquareProduct W).compl₂ e.toLinearMap).comp e.toLinearMap)
    (fun v w ↦ symmetricSquareProduct_comm W (e v) (e w)) v w).symm

/-- The actual inclusion square for U and its coordinate image commutes.
Source: support in the original symmetric quotient. -/
theorem saturationSymmetricSquareEquiv_subtype (e : V ≃ₗ[ℝ] W) (U : Submodule ℝ V) :
    (saturationSymmetricSquareEquiv e).toLinearMap.comp
        (symmetricSquareLinearMap U.subtype) =
      (symmetricSquareLinearMap (U.map e.toLinearMap).subtype).comp
        (saturationSymmetricSquareEquiv (e.submoduleMap U)).toLinearMap := by
  apply (symmetricSquareRelations U).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change saturationSymmetricSquareEquiv e
      (symmetricSquareLinearMap U.subtype (symmetricSquareProduct U v w)) =
    symmetricSquareLinearMap (U.map e.toLinearMap).subtype
      (saturationSymmetricSquareEquiv (e.submoduleMap U) (symmetricSquareProduct U v w))
  rw [show symmetricSquareLinearMap U.subtype (symmetricSquareProduct U v w) =
    symmetricSquareProduct V (v : V) (w : V) from
      symmetricBilinearDescend_product _ _ v w]
  rw [saturationSymmetricSquareEquiv_product, saturationSymmetricSquareEquiv_product]
  exact (symmetricBilinearDescend_product
    (((symmetricSquareProduct W).compl₂ (U.map e.toLinearMap).subtype).comp
      (U.map e.toLinearMap).subtype)
    (fun v w ↦ symmetricSquareProduct_comm W (v : W) (w : W))
    ((e.submoduleMap U) v) ((e.submoduleMap U) w)).symm

/-- Actual symmetric-square support is transported in both directions.
Source: original supporting-subspace conclusion, with no extra support input. -/
theorem saturationSymmetricSquareEquiv_mem_range (e : V ≃ₗ[ℝ] W)
    (U : Submodule ℝ V) (q : SymmetricSquare V) :
    q ∈ LinearMap.range (symmetricSquareLinearMap U.subtype) ↔
      saturationSymmetricSquareEquiv e q ∈
        LinearMap.range (symmetricSquareLinearMap (U.map e.toLinearMap).subtype) := by
  have hs (r : SymmetricSquare U) := congrArg
    (fun L : SymmetricSquare U →ₗ[ℝ] SymmetricSquare W ↦ L r)
    (saturationSymmetricSquareEquiv_subtype e U)
  simp only [LinearMap.comp_apply, LinearEquiv.coe_coe] at hs
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨saturationSymmetricSquareEquiv (e.submoduleMap U) r, (hs r).symm⟩
  · rintro ⟨r, hr⟩
    refine ⟨(saturationSymmetricSquareEquiv (e.submoduleMap U)).symm r, ?_⟩
    apply (saturationSymmetricSquareEquiv e).injective
    rw [hs]
    change symmetricSquareLinearMap (U.map e.toLinearMap).subtype
      (saturationSymmetricSquareEquiv (e.submoduleMap U)
        ((saturationSymmetricSquareEquiv (e.submoduleMap U)).symm r)) = _
    rw [LinearEquiv.apply_symm_apply]
    exact hr

end Algebraic

section Normed
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Native finite-dimensional coordinates; no isometry is asserted.
Source: internal Euclidean reduction in the saturation proof. -/
def saturationEuclideanCoordinates :
    V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
  ContinuousLinearEquiv.ofFinrankEq finrank_euclideanSpace_fin.symm

/-- The FULL original continuous dual is parametrized by Euclidean points.
This is a native CLE, so open sets transport honestly despite the changed metric.
Source: good covectors in the original saturation proof. -/
def saturationEuclideanCovectors :
    EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) ≃L[ℝ] (V →L[ℝ] ℝ) :=
  let E := EuclideanSpace ℝ (Fin (Module.finrank ℝ V))
  (InnerProductSpace.toDual ℝ E).toContinuousLinearEquiv.trans
    ((saturationEuclideanCoordinates V).symm.arrowCongr (ContinuousLinearEquiv.refl ℝ ℝ))

/-- The exact pulled-back Riesz functional on the original normed space.
Source: actual contraction covectors, without an inner product on V. -/
theorem saturationEuclideanCovectors_apply
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) (v : V) :
    saturationEuclideanCovectors V x v = inner ℝ x (saturationEuclideanCoordinates V v) := rfl

/-- Actual algebraic model of the SAME original symmetric square.
The original normed space V is not supplied an inner product.
Source: applying the Euclidean quadratic-space theorem internally. -/
def saturationEuclideanModel : SymmetricSquare V ≃ₗ[ℝ]
    selfAdjoint (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
  (saturationSymmetricSquareEquiv (saturationEuclideanCoordinates V).toLinearEquiv).trans
    symmetricSquareSelfAdjointEquiv

/-- Exact formula identifying the model with the canonical quotient functor.
Source: the original tensor/operator dictionary in Euclidean coordinates. -/
theorem saturationEuclideanModel_apply (q : SymmetricSquare V) :
    saturationEuclideanModel V q = symmetricSquareToSelfAdjoint
      (symmetricSquareLinearMap (saturationEuclideanCoordinates V).toLinearMap q) := by
  change symmetricSquareSelfAdjointEquiv
    (saturationSymmetricSquareEquiv (saturationEuclideanCoordinates V).toLinearEquiv q) = _
  have h := congrArg (fun L : SymmetricSquare V →ₗ[ℝ]
    SymmetricSquare (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) ↦ L q)
    (saturationSymmetricSquareEquiv_toLinearMap
      (saturationEuclideanCoordinates V).toLinearEquiv)
  rw [show saturationSymmetricSquareEquiv (saturationEuclideanCoordinates V).toLinearEquiv q =
    symmetricSquareLinearMap (saturationEuclideanCoordinates V).toLinearMap q from h]
  rfl

/-- The actual continuous operator underlying the algebraic model.
Source: the operator subspace to which the genuine Euclidean theorem applies. -/
def saturationEuclideanOperator : SymmetricSquare V →ₗ[ℝ]
    (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) where
  toFun q := (saturationEuclideanModel V q).val
  map_add' p q := congrArg Subtype.val ((saturationEuclideanModel V).map_add p q)
  map_smul' c q := congrArg Subtype.val ((saturationEuclideanModel V).map_smul c q)

/-- The actual operator model is injective, not just dimension non-increasing.
Source: faithful transport of the original saturation intersection. -/
theorem saturationEuclideanOperator_injective :
    Function.Injective (saturationEuclideanOperator V) := by
  intro p q hpq
  apply (saturationEuclideanModel V).injective
  exact Subtype.ext hpq

/-- Every operator in the actual image subspace is symmetric.
Source: application of the real quadratic-space bound/classification. -/
theorem saturationEuclideanOperator_symmetric
    (K : Submodule ℝ (SymmetricSquare V)) :
    ∀ Q ∈ K.map (saturationEuclideanOperator V), Q.toLinearMap.IsSymmetric := by
  rintro _ ⟨q, _, rfl⟩
  exact (saturationEuclideanModel V q).property.isSymmetric

/-- The actual CLM image subspace has precisely the original dimension.
Source: SAME-R dimension, without changing its original carrier. -/
theorem saturationEuclideanOperator_finrank (K : Submodule ℝ (SymmetricSquare V)) :
    Module.finrank ℝ K = Module.finrank ℝ (K.map (saturationEuclideanOperator V)) :=
  (Submodule.equivMapOfInjective _ (saturationEuclideanOperator_injective V) K).finrank_eq

/-- SAME original subspace support iff actual model operator range support.
Source: literal supporting-subspace classification for the original quotient. -/
theorem saturationEuclideanModel_support (U : Submodule ℝ V) (q : SymmetricSquare V) :
    q ∈ LinearMap.range (symmetricSquareLinearMap U.subtype) ↔
      LinearMap.range (saturationEuclideanModel V q).val.toLinearMap ≤
        U.map (saturationEuclideanCoordinates V).toLinearMap := by
  rw [saturationSymmetricSquareEquiv_mem_range
    (saturationEuclideanCoordinates V).toLinearEquiv U q,
    symmetricSquare_mem_range_iff_operator_range]
  rfl

/-- Support on any Euclidean subspace pulls back to the literal original subspace.
Source: pullback of the supporting hyperplane in the equality case. -/
theorem saturationEuclideanModel_support_comap
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))))
    (q : SymmetricSquare V) :
    q ∈ LinearMap.range (symmetricSquareLinearMap
        (S.comap (saturationEuclideanCoordinates V).toLinearMap).subtype) ↔
      LinearMap.range (saturationEuclideanModel V q).val.toLinearMap ≤ S := by
  rw [saturationEuclideanModel_support,
    Submodule.map_comap_eq_of_surjective (saturationEuclideanCoordinates V).surjective]

/-- The exact full supported operator space is the image of the original support.
Source: equality classification pulled back through the genuine model. -/
theorem saturationEuclideanOperator_supported_image
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))) :
    (LinearMap.range (symmetricSquareLinearMap
      (S.comap (saturationEuclideanCoordinates V).toLinearMap).subtype)).map
        (saturationEuclideanOperator V) = quadraticSpaceSupportedOperators S := by
  apply le_antisymm
  · rintro _ ⟨q, hq, rfl⟩
    refine ⟨(saturationEuclideanModel V q).property.isSymmetric, ?_⟩
    intro x
    exact (saturationEuclideanModel_support_comap V S q).mp hq ⟨x, rfl⟩
  · intro Q hQ
    let A : selfAdjoint (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
        EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :=
      ⟨Q, ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr hQ.1⟩
    let q := (saturationEuclideanModel V).symm A
    have hq : saturationEuclideanModel V q = A :=
      (saturationEuclideanModel V).apply_symm_apply A
    refine ⟨q, (saturationEuclideanModel_support_comap V S q).mpr ?_, ?_⟩
    · rw [hq]
      rintro _ ⟨x, rfl⟩
      exact hQ.2 x
    · exact congrArg Subtype.val hq

/-- Equality with the full supported operator space pulls back exactly.
Source: the original supporting-hyperplane equality case, preserving the full space. -/
theorem saturationEuclideanOperator_supported_iff
    (K : Submodule ℝ (SymmetricSquare V))
    (S : Submodule ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))) :
    K.map (saturationEuclideanOperator V) = quadraticSpaceSupportedOperators S ↔
      K = LinearMap.range (symmetricSquareLinearMap
        (S.comap (saturationEuclideanCoordinates V).toLinearMap).subtype) := by
  rw [← saturationEuclideanOperator_supported_image V S]
  exact (Submodule.map_injective_of_injective
    (saturationEuclideanOperator_injective V)).eq_iff

/-- Actual dimensions of all original quotient subspaces are preserved.
Source: SAME-R dimension transfer in the original saturation argument. -/
theorem saturationEuclideanModel_finrank (K : Submodule ℝ (SymmetricSquare V)) :
    Module.finrank ℝ K =
      Module.finrank ℝ (K.map (saturationEuclideanModel V).toLinearMap) :=
  ((saturationEuclideanModel V).submoduleMap K).finrank_eq

/-- Actual dimensions of original supporting subspaces are preserved.
Source: pullback of the literal supporting hyperplane, including zero dimension. -/
theorem saturationEuclideanCoordinates_finrank (U : Submodule ℝ V) :
    Module.finrank ℝ U =
      Module.finrank ℝ (U.map (saturationEuclideanCoordinates V).toLinearMap) :=
  ((saturationEuclideanCoordinates V).toLinearEquiv.submoduleMap U).finrank_eq

end Normed
end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturationEuclideanCoordinates
#print axioms GlobalEmbedding.Paper.saturationEuclideanCoordinates_finrank
#print axioms GlobalEmbedding.Paper.saturationEuclideanCovectors
#print axioms GlobalEmbedding.Paper.saturationEuclideanCovectors_apply
#print axioms GlobalEmbedding.Paper.saturationEuclideanModel
#print axioms GlobalEmbedding.Paper.saturationEuclideanModel_apply
#print axioms GlobalEmbedding.Paper.saturationEuclideanModel_finrank
#print axioms GlobalEmbedding.Paper.saturationEuclideanModel_support
#print axioms GlobalEmbedding.Paper.saturationEuclideanModel_support_comap
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_finrank
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_injective
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_supported_iff
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_supported_image
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_symmetric
#print axioms GlobalEmbedding.Paper.saturationSymmetricSquareEquiv
#print axioms GlobalEmbedding.Paper.saturationSymmetricSquareEquiv_mem_range
#print axioms GlobalEmbedding.Paper.saturationSymmetricSquareEquiv_product
#print axioms GlobalEmbedding.Paper.saturationSymmetricSquareEquiv_subtype
#print axioms GlobalEmbedding.Paper.saturationSymmetricSquareEquiv_toLinearMap
