import GlobalEmbedding.Paper.SymmetricSquare
import Mathlib.Analysis.InnerProductSpace.TensorProduct

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

/-- The tensor square of a linear map preserves the antisymmetric relations.
Proof: each generating difference maps to the same difference of the two images.
Source: `prop:initialization`, second-jet transport. -/
theorem symmetricSquareMap_preservesRelations (f : E →L[ℝ] F) :
    symmetricSquareRelations E ≤ (symmetricSquareRelations F).comap
      (TensorProduct.map f.toLinearMap f.toLinearMap) := by
  rw [symmetricSquareRelations]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨v, w⟩, rfl⟩
  change TensorProduct.map f.toLinearMap f.toLinearMap
    (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) ∈ symmetricSquareRelations F
  rw [map_sub, TensorProduct.map_tmul, TensorProduct.map_tmul]
  exact Submodule.subset_span ⟨(f v, f w), rfl⟩

end GlobalEmbedding.Paper
