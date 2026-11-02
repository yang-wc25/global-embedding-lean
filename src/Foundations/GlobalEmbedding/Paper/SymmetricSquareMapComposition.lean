import GlobalEmbedding.Paper.SymmetricSquareMap

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Functoriality of transport on the exact binary quotient.
Proof: quotient representatives reduce it to the tensor product map composition law.
Source: `prop:initialization`, transport of second forms. -/
theorem symmetricSquareMap_comp (g : F →L[ℝ] G) (f : E →L[ℝ] F)
    (z : SymmetricSquare E) :
    symmetricSquareMap g (symmetricSquareMap f z) = symmetricSquareMap (g.comp f) z := by
  induction z using Submodule.Quotient.induction_on with
  | _ a =>
    simp only [symmetricSquareMap_mk, TensorProduct.map_map]
    rfl

end GlobalEmbedding.Paper
