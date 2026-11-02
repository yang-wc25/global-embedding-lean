import Probes.ActualIncrementSymmetricCoordinates
import GlobalEmbedding.Paper.SymmetricSquareLinearEquivalence
import GlobalEmbedding.Paper.SymmetricSquareLinearMap

/-! Surjectivity of the existing sorted coordinates in the original binary
symmetric quotient. This supplies the reverse transverse-frame/Good bridge;
no alternative tensor carrier or normalization is introduced. -/
noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped TensorProduct BigOperators
namespace GlobalEmbedding.Continuation

theorem round3_prepared_symmetric_map_product
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (f : E →ₗ[ℝ] F) (v w : E) :
    symmetricSquareLinearMap f (symmetricSquareProduct E v w) = symmetricSquareProduct F (f v) (f w) :=
  symmetricBilinearDescend_product (((symmetricSquareProduct F).compl₂ f).comp f)
    (fun v w => symmetricSquareProduct_comm F (f v) (f w)) v w

theorem round3_prepared_symmetric_equiv_surjective
    {E F : Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
    (e : E ≃ₗ[ℝ] F) : Function.Surjective (symmetricSquareLinearMap e.toLinearMap) := by
  have hcomp : (symmetricSquareLinearMap e.toLinearMap).comp
      (symmetricSquareLinearMap e.symm.toLinearMap) = LinearMap.id := by
    apply (symmetricSquareRelations F).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change symmetricSquareLinearMap e.toLinearMap
      (symmetricSquareLinearMap e.symm.toLinearMap (symmetricSquareProduct F v w)) = symmetricSquareProduct F v w
    rw [round3_prepared_symmetric_map_product,round3_prepared_symmetric_map_product]
    simp only [LinearEquiv.coe_coe,LinearEquiv.apply_symm_apply]
  intro w
  refine ⟨symmetricSquareLinearMap e.symm.toLinearMap w,?_⟩
  exact congrArg (fun L : SymmetricSquare F →ₗ[ℝ] SymmetricSquare F => L w) hcomp

theorem round3_prepared_sorted_symmetric_surjective (m : ℕ) :
    Function.Surjective (actualIncrementSortedSymmetricLinear m) := by
  classical
  let S := actualIncrementSortedSymmetricLinear m
  let D := EuclideanSpace ℝ (Fin m)
  have hSorted (i j : Fin m) (hij : i ≤ j) :
      symmetricSquareProduct D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ∈ LinearMap.range S := by
    refine ⟨EuclideanSpace.single ⟨(i,j),hij⟩ 1,?_⟩
    simp [S,D,actualIncrementSortedSymmetricLinear_apply,PiLp.single_apply]
  have hCoord (i j : Fin m) :
      symmetricSquareProduct D (EuclideanSpace.single i 1) (EuclideanSpace.single j 1) ∈ LinearMap.range S := by
    rcases le_total i j with hij | hji
    · exact hSorted i j hij
    · rw [symmetricSquareProduct_comm]
      exact hSorted j i hji
  have hExpansion (v : D) : v = ∑ i : Fin m, (v i) • EuclideanSpace.single i 1 := by
    ext i
    simp [D,Pi.single_apply,eq_comm]
  have hProduct (v w : D) : symmetricSquareProduct D v w ∈ LinearMap.range S := by
    rw [hExpansion v,hExpansion w]
    simp only [map_sum,map_smul,LinearMap.sum_apply,LinearMap.smul_apply]
    apply Submodule.sum_mem
    intro j hj
    apply Submodule.smul_mem
    apply Submodule.sum_mem
    intro i hi
    exact Submodule.smul_mem _ _ (hCoord i j)
  intro q
  change q ∈ LinearMap.range S
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w => exact hProduct v w
    | add t u ht hu =>
      change symmetricSquareQuotient D (t+u) ∈ LinearMap.range S
      rw [map_add]
      exact (LinearMap.range S).add_mem ht hu

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_sorted_symmetric_surjective
#print axioms GlobalEmbedding.Continuation.round3_prepared_symmetric_equiv_surjective
