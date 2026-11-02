import GlobalEmbedding.Paper.SymmetricBilinearDescend

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The descended map evaluates on the canonical product as the original bilinear map.
Proof: both quotient lift and tensor lift compute on their generators.
Source: `defn:phase`, B(v⊙w)=β(v,w) on the project's exact binary quotient. -/
@[simp] theorem symmetricBilinearDescend_product (β : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (hβ : ∀ v w, β v w = β w v) (v w : V) :
    symmetricBilinearDescend β hβ (symmetricSquareProduct V v w) = β v w := by
  rw [symmetricSquareProduct_apply, symmetricBilinearDescend]
  simp [symmetricSquareQuotient]

end GlobalEmbedding.Paper
