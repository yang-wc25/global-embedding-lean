import GlobalEmbedding.Paper.HilbertSchmidtCoordinateEvaluation

/-!
# Exact sum formula for actual Hilbert–Schmidt coordinate evaluation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-hilbert-schmidt-evaluation-formula`.
-/

namespace GlobalEmbedding.Paper

/-- The constructed evaluation is exactly matrix-vector multiplication in canonical flat
coefficient coordinates. This is definitional through Mathlib's Euclidean matrix equivalence.
Source: pointwise operator multiplication in `lem:balanced`. -/
theorem hilbertSchmidt_coordinate_evaluation_formula (M N : ℕ)
    (A : EuclideanSpace ℝ (Fin (N * M))) (u : EuclideanSpace ℝ (Fin M)) (i : Fin N) :
    hilbertSchmidtCoordinateEvaluation M N A u i =
      ∑ j : Fin M, A (finProdFinEquiv (i, j)) * u j := by
  rfl

#print axioms hilbertSchmidt_coordinate_evaluation_formula

end GlobalEmbedding.Paper
