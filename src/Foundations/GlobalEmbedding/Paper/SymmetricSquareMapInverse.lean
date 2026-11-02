import GlobalEmbedding.Paper.SymmetricSquareMapComposition
import GlobalEmbedding.Paper.SymmetricSquareMapIdentity

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- Transport by the inverse is inverse transport on the binary quotient.
Source: `prop:initialization`, invertibility of symmetric-square transport. -/
@[simp] theorem symmetricSquareMap_symm (e : E ≃L[ℝ] F) (z : SymmetricSquare E) :
    symmetricSquareMap e.symm.toContinuousLinearMap
      (symmetricSquareMap e.toContinuousLinearMap z) = z := by
  rw [symmetricSquareMap_comp]
  have he : e.symm.toContinuousLinearMap.comp e.toContinuousLinearMap =
      ContinuousLinearMap.id ℝ E := by ext x; simp
  rw [he, symmetricSquareMap_id]

end GlobalEmbedding.Paper
