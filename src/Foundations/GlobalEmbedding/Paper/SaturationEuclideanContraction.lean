import GlobalEmbedding.Paper.SaturationEuclideanModel
import GlobalEmbedding.Paper.ContractionCovectorFamily

/-!
# Exact original contraction and evaluation ranges in the Euclidean model

Source: original `prop:saturation`, lines948–995.
DAG: saturation-euclidean-contraction-transfer. Exclusive W1.
This adapter reuses W2 no-IP naturality; it does not reconstruct the contraction
family or impose an inner product on the original normed source.
-/

noncomputable section
namespace GlobalEmbedding.Paper
variable (V : Type*) [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]

/-- Actual model evaluation is the coordinate image of the SAME original contraction.
Source: the covector/operator dictionary for the original saturation intersection. -/
theorem saturationEuclideanOperator_contraction (q : SymmetricSquare V)
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :
    saturationEuclideanOperator V q x = saturationEuclideanCoordinates V
      (contractionKernelQuotientMap (saturationEuclideanCovectors V x).toLinearMap q) := by
  change (saturationEuclideanModel V q).val x = _
  rw [saturationEuclideanModel_apply, symmetricSquareToSelfAdjoint_apply]
  have hx : (saturationEuclideanCovectors V x).toLinearMap =
      (innerₗ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) x).comp
        (saturationEuclideanCoordinates V).toLinearMap := by
    ext v
    rfl
  rw [hx]
  exact (contractionKernelQuotientMap_naturality_apply
    (saturationEuclideanCoordinates V).toLinearMap
    (innerₗ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) x) q).symm

/-- Exact evaluation range of the actual mapped original subspace, at EVERY point.
Source: the SAME-R evaluation bound, before choosing any good or maximal point. -/
theorem saturationEuclideanOperator_evaluation_range
    (K : Submodule ℝ (SymmetricSquare V))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :
    LinearMap.range (quadraticSpaceEvaluation
        (K.map (saturationEuclideanOperator V)) x).toLinearMap =
      (K.map (contractionKernelQuotientMap
        (saturationEuclideanCovectors V x).toLinearMap)).map
          (saturationEuclideanCoordinates V).toLinearMap := by
  apply le_antisymm
  · rintro _ ⟨Q, rfl⟩
    obtain ⟨q, hq, heq⟩ := Submodule.mem_map.mp Q.property
    change (Q : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ]
      EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) x ∈ _
    rw [← heq, saturationEuclideanOperator_contraction]
    exact ⟨_, ⟨q, hq, rfl⟩, rfl⟩
  · rintro _ ⟨_, ⟨q, hq, rfl⟩, rfl⟩
    refine ⟨⟨saturationEuclideanOperator V q, ⟨q, hq, rfl⟩⟩, ?_⟩
    exact saturationEuclideanOperator_contraction V q x

/-- Exact dimension transfer of that actual evaluation range, at EVERY point.
Source: faithful use of the Euclidean dimension/equality theorem on the original R. -/
theorem saturationEuclideanOperator_evaluation_finrank
    (K : Submodule ℝ (SymmetricSquare V))
    (x : EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) :
    Module.finrank ℝ (LinearMap.range (quadraticSpaceEvaluation
        (K.map (saturationEuclideanOperator V)) x).toLinearMap) =
      Module.finrank ℝ (K.map (contractionKernelQuotientMap
        (saturationEuclideanCovectors V x).toLinearMap)) := by
  rw [saturationEuclideanOperator_evaluation_range]
  exact (saturationEuclideanCoordinates V).toLinearEquiv.finrank_map_eq _

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_contraction
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_evaluation_range
#print axioms GlobalEmbedding.Paper.saturationEuclideanOperator_evaluation_finrank
