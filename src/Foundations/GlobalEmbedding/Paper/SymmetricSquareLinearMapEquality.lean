import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import GlobalEmbedding.Paper.SymmetricBilinearDescendUnique
import GlobalEmbedding.Paper.SymmetricSquareMapProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

/-- The purely algebraic functor is the existing entire normed quotient map.
Proof: uniqueness of the already proved symmetric bilinear descent, using the
existing exact continuous-map product formula. Source: `defn:phase`, canonical
restriction independent of auxiliary norms and normalization. -/
theorem symmetric_square_linear_map_eq
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] (f : E →L[ℝ] F) :
    symmetricSquareLinearMap f.toLinearMap = symmetricSquareMap f := by
  unfold symmetricSquareLinearMap
  symm
  apply symmetricBilinearDescend_unique
  intro v w
  exact symmetricSquareMapL_product f v w

end GlobalEmbedding.Paper
