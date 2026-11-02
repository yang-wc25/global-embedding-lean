import GlobalEmbedding.Paper.SymmetricBilinearRelations

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The canonical linear descent of a symmetric bilinear map through the exact
binary SymmetricSquare quotient. Well-definedness uses the named proved relation lemma.
Source: `defn:phase`, normal second form on Sym², with no normalization factor. -/
noncomputable def symmetricBilinearDescend (β : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (hβ : ∀ v w, β v w = β w v) : SymmetricSquare V →ₗ[ℝ] W :=
  (symmetricSquareRelations V).liftQ (TensorProduct.lift β)
    (symmetricBilinear_killsRelations β hβ)

end GlobalEmbedding.Paper
