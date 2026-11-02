import GlobalEmbedding.Paper.SymmetricSquareMapRelations
import GlobalEmbedding.Paper.SymmetricSquareNorms
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Quotient

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

/-- The induced map is continuous with the proved square operator bound.
Source: `prop:initialization`, uniform symmetric-square transport. -/
noncomputable def symmetricSquareMapL (f : E →L[ℝ] F) :
    SymmetricSquare E →L[ℝ] SymmetricSquare F :=
  (symmetricSquareRelations E).liftQL
    ((symmetricSquareRelations F).mkQL.comp (TensorProduct.mapL f f)) (by
      intro z hz
      change (symmetricSquareRelations F).mkQL ((TensorProduct.mapL f f) z) = 0
      change (Submodule.Quotient.mk ((TensorProduct.mapL f f) z) : SymmetricSquare F) = 0
      rw [TensorProduct.mapL_apply]
      exact (Submodule.Quotient.mk_eq_zero (symmetricSquareRelations F)).mpr
        (symmetricSquareMap_preservesRelations f hz))

end GlobalEmbedding.Paper
