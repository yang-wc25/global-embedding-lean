import GlobalEmbedding.Paper.SymmetricSquareMapRelations

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The induced linear map on the exact binary symmetric-square quotient.
Source: `prop:initialization`, transport of the selector form. -/
noncomputable def symmetricSquareMap (f : E →L[ℝ] F) :
    SymmetricSquare E →ₗ[ℝ] SymmetricSquare F :=
  (symmetricSquareRelations E).mapQ (symmetricSquareRelations F)
    (TensorProduct.map f.toLinearMap f.toLinearMap)
    (symmetricSquareMap_preservesRelations f)

/-- A quotient representative maps to the class of its tensor-square image.
Source: the quotient map in `prop:initialization`. -/
@[simp] theorem symmetricSquareMap_mk (f : E →L[ℝ] F) (z : E ⊗[ℝ] E) :
    symmetricSquareMap f (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk (TensorProduct.map f.toLinearMap f.toLinearMap z) := rfl

end GlobalEmbedding.Paper
