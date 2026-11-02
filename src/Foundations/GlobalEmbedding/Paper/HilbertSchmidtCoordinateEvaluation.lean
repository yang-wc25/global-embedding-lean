import GlobalEmbedding.Paper.HilbertSchmidtCoordinateEquiv

/-!
# Actual continuous bilinear evaluation of Hilbert–Schmidt operator coordinates

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-hilbert-schmidt-evaluation`.
-/

namespace GlobalEmbedding.Paper

/-- Actual operator evaluation from the Euclidean Hilbert–Schmidt coordinates, as a continuous
bilinear map. The faithful coordinate equivalence supplies the exact operator for each vector;
finite-dimensionality makes its forward linear map continuous. No coefficient action is assumed.
Source: matrix-valued pointwise multiplication in the proof of `lem:balanced`. -/
noncomputable def hilbertSchmidtCoordinateEvaluation (M N : ℕ) :
    EuclideanSpace ℝ (Fin (N * M)) →L[ℝ]
      EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (hilbertSchmidtCoordinateEquiv M N).toLinearMap.toContinuousLinearMap

#print axioms hilbertSchmidtCoordinateEvaluation

end GlobalEmbedding.Paper
