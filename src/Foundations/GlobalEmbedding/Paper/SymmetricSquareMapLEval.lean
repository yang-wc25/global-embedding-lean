import GlobalEmbedding.Paper.SymmetricSquareMapL
import GlobalEmbedding.Paper.SymmetricSquareMap
import GlobalEmbedding.Paper.SymmetricSquareNorms

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

/-- Evaluation of the continuous map agrees with the algebraic quotient map.
Source: `prop:initialization`, the same binary symmetric-square transport. -/
@[simp] theorem symmetricSquareMapL_apply (f : E →L[ℝ] F) (z : SymmetricSquare E) :
    symmetricSquareMapL f z = symmetricSquareMap f z := by
  induction z using Submodule.Quotient.induction_on with
  | _ a => simp [symmetricSquareMapL, symmetricSquareMap]

end GlobalEmbedding.Paper
