import GlobalEmbedding.Paper.HilbertSchmidtCoordinateEvaluationFormula

/-!
# Exact Hilbert–Schmidt calibration of the actual Euclidean coefficient norm

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-hilbert-schmidt-norm`.
-/

namespace GlobalEmbedding.Paper

/-- The actual Euclidean coefficient norm is exactly the Hilbert–Schmidt norm: its square is
the sum of squared norms of the represented operator on the standard orthonormal basis.

Expand both actual Euclidean norms into coordinate squares. Evaluation on a basis vector
picks one matrix column, and the canonical product-index bijection identifies the two finite
sums. This calibrates Hilbert–Schmidt rather than the default operator norm.
Source: Euclidean coefficient norm for Holder operator multiplication in `lem:balanced`. -/
theorem hilbertSchmidt_coordinate_norm (M N : ℕ) (A : EuclideanSpace ℝ (Fin (N * M))) :
    ‖A‖ ^ 2 = ∑ j : Fin M,
      ‖hilbertSchmidtCoordinateEvaluation M N A (EuclideanSpace.single j 1)‖ ^ 2 := by
  have hcolumn (j : Fin M) (i : Fin N) :
      hilbertSchmidtCoordinateEvaluation M N A (EuclideanSpace.single j 1) i =
        A (finProdFinEquiv (i, j)) := by
    rw [hilbertSchmidt_coordinate_evaluation_formula]
    simp [EuclideanSpace.single, PiLp.single_apply]
  calc
    _ = ∑ p : Fin N × Fin M, (A (finProdFinEquiv p)) ^ 2 := by
      rw [EuclideanSpace.real_norm_sq_eq]
      exact (finProdFinEquiv.sum_comp (fun r ↦ (A r) ^ 2)).symm
    _ = ∑ j : Fin M, ∑ i : Fin N, (A (finProdFinEquiv (i, j))) ^ 2 := by
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    _ = _ := by
      apply Finset.sum_congr rfl
      intro j hj
      rw [EuclideanSpace.real_norm_sq_eq]
      apply Finset.sum_congr rfl
      intro i hi
      rw [hcolumn]

#print axioms hilbertSchmidt_coordinate_norm

end GlobalEmbedding.Paper
