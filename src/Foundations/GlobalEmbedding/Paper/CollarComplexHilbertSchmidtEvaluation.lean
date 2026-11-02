import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual complex Hilbert–Schmidt coefficient evaluation

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534, and `lem:balanced`, lines 396–418. The flat coefficient index agrees
with the actual Gram inverse matrix and the real Hilbert–Schmidt multiplier.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Actual complex flat coefficients represent all finite-dimensional complex value operators.
Use the explicit product-index bijection and the Euclidean matrix-to-linear-map equivalence.
The coefficient norm remains the Euclidean Hilbert–Schmidt norm, calibrated below. -/
noncomputable def collarComplexHilbertSchmidtEquiv (M N : ℕ) :
    EuclideanSpace ℂ (Fin (N * M)) ≃ₗ[ℂ]
      (EuclideanSpace ℂ (Fin M) →L[ℂ] EuclideanSpace ℂ (Fin N)) := by
  let e : EuclideanSpace ℂ (Fin (N * M)) ≃ₗ[ℂ] Matrix (Fin N) (Fin M) ℂ :=
    { toFun := fun A i j ↦ A (finProdFinEquiv (i, j))
      invFun := fun A ↦ toLp 2 (fun r ↦
        A (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)
      left_inv := by
        intro A
        ext r
        change A (finProdFinEquiv (finProdFinEquiv.symm r)) = A r
        exact congrArg (fun s ↦ A s) (finProdFinEquiv.apply_symm_apply r)
      right_inv := by
        intro A
        ext i j
        change A (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
          (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = A i j
        simp
      map_add' := by intro A B; ext i j; rfl
      map_smul' := by intro c A; ext i j; rfl }
  exact e.trans (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)

/-- Actual continuous complex bilinear matrix-vector multiplication in flat coordinates.
Finite-dimensionality makes the faithful coefficient-to-operator linear map continuous. -/
noncomputable def collarComplexHilbertSchmidtEvaluation (M N : ℕ) :
    EuclideanSpace ℂ (Fin (N * M)) →L[ℂ]
      EuclideanSpace ℂ (Fin M) →L[ℂ] EuclideanSpace ℂ (Fin N) :=
  (collarComplexHilbertSchmidtEquiv M N).toLinearMap.toContinuousLinearMap

/-- The actual complex coefficient evaluation has exactly the canonical matrix-vector formula.
It is definitional through the Euclidean matrix equivalence. -/
theorem collar_complex_hilbert_schmidt_evaluation_formula (M N : ℕ)
    (A : EuclideanSpace ℂ (Fin (N * M))) (u : EuclideanSpace ℂ (Fin M)) (i : Fin N) :
    collarComplexHilbertSchmidtEvaluation M N A u i =
      ∑ j : Fin M, A (finProdFinEquiv (i, j)) * u j := rfl

/-- The original Euclidean complex coefficient norm is exactly Hilbert–Schmidt.
Expand both norms into coordinate norm squares, evaluate on the standard basis, and reindex
by the canonical product-index bijection. This includes either empty value dimension. -/
theorem collar_complex_hilbert_schmidt_norm (M N : ℕ)
    (A : EuclideanSpace ℂ (Fin (N * M))) :
    ‖A‖ ^ 2 = ∑ j : Fin M,
      ‖collarComplexHilbertSchmidtEvaluation M N A (EuclideanSpace.single j 1)‖ ^ 2 := by
  have hcolumn (j : Fin M) (i : Fin N) :
      collarComplexHilbertSchmidtEvaluation M N A (EuclideanSpace.single j 1) i =
        A (finProdFinEquiv (i, j)) := by
    rw [collar_complex_hilbert_schmidt_evaluation_formula]
    simp [EuclideanSpace.single, PiLp.single_apply]
  calc
    _ = ∑ p : Fin N × Fin M, ‖A (finProdFinEquiv p)‖ ^ 2 := by
      rw [EuclideanSpace.norm_sq_eq]
      exact (finProdFinEquiv.sum_comp (fun r ↦ ‖A r‖ ^ 2)).symm
    _ = ∑ j : Fin M, ∑ i : Fin N, ‖A (finProdFinEquiv (i, j))‖ ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [EuclideanSpace.norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcolumn]

/-- Real coefficients and vectors evaluate to the actual real matrix-vector sum, embedded in ℂ.
This follows coordinatewise from the exact complex evaluation and preservation of finite sums
and products by the real inclusion. No real multiplier data are assumed. -/
theorem collar_complex_hilbert_schmidt_real_formula (M N : ℕ)
    (A : EuclideanSpace ℝ (Fin (N * M))) (u : EuclideanSpace ℝ (Fin M)) :
    collarComplexHilbertSchmidtEvaluation M N
      (toLp 2 (fun r ↦ (A r : ℂ))) (toLp 2 (fun j ↦ (u j : ℂ))) =
        toLp 2 (fun i : Fin N ↦ ((∑ j : Fin M,
          A (finProdFinEquiv (i, j)) * u j : ℝ) : ℂ)) := by
  ext i
  rw [collar_complex_hilbert_schmidt_evaluation_formula]
  simp

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarComplexHilbertSchmidtEquiv
#print axioms GlobalEmbedding.Paper.collarComplexHilbertSchmidtEvaluation
#print axioms GlobalEmbedding.Paper.collar_complex_hilbert_schmidt_norm
#print axioms GlobalEmbedding.Paper.collar_complex_hilbert_schmidt_real_formula
