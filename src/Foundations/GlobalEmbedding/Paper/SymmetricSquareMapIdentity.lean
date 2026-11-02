import GlobalEmbedding.Paper.SymmetricSquareMap

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The identity induces the identity on the binary quotient.
Source: `prop:initialization`, functorial transport. -/
@[simp] theorem symmetricSquareMap_id (z : SymmetricSquare E) :
    symmetricSquareMap (ContinuousLinearMap.id ℝ E) z = z := by
  induction z using Submodule.Quotient.induction_on with
  | _ a => simp [symmetricSquareMap_mk, TensorProduct.map_id]

end GlobalEmbedding.Paper
