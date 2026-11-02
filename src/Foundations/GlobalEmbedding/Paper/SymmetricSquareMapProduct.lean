import GlobalEmbedding.Paper.SymmetricSquareMapLEval

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

/-- The existing continuous transport preserves the exact canonical quotient product.
Proof: evaluate its original tensor-square quotient lift on a pure tensor.
Source: actual symmetric-square bundle chart transitions in `defn:phase`. -/
theorem symmetricSquareMapL_product
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    (A : E →L[ℝ] F) (v w : E) :
    symmetricSquareMapL A (symmetricSquareProduct E v w) =
      symmetricSquareProduct F (A v) (A w) := by
  rw [symmetricSquareMapL_apply]
  simp only [symmetricSquareProduct_apply, symmetricSquareMap]
  rfl

end GlobalEmbedding.Paper
