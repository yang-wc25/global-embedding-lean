import GlobalEmbedding.Paper.SymmetricSquareMapInverse
import GlobalEmbedding.Paper.SymmetricSquareMapNorm
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

/-- Inverse transport controls the norm of a symmetric tensor by the square inverse bound.
Source: `prop:initialization`, preservation of the selector margin under transport. -/
theorem symmetricSquareMap_inverse_norm_bound (e : E ≃L[ℝ] F) (z : SymmetricSquare E) :
    ‖z‖ ≤ ‖e.symm.toContinuousLinearMap‖ ^ 2 *
      ‖symmetricSquareMap e.toContinuousLinearMap z‖ := by
  simpa only [symmetricSquareMap_symm] using
    symmetricSquareMap_norm_le e.symm.toContinuousLinearMap
      (symmetricSquareMap e.toContinuousLinearMap z)

end GlobalEmbedding.Paper
