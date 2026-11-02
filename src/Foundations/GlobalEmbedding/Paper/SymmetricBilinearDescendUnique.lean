import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Every linear map with the required product values is the canonical descent.
Proof: compose with the surjective quotient map. Tensor product extensionality reduces
equality of the compositions to the pure tensor values, which are prescribed.
Source: `defn:phase`, uniqueness of the symmetric-square realization. -/
theorem symmetricBilinearDescend_unique (β : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (hβ : ∀ v w, β v w = β w v) (B : SymmetricSquare V →ₗ[ℝ] W)
    (hB : ∀ v w, B (symmetricSquareProduct V v w) = β v w) :
    B = symmetricBilinearDescend β hβ := by
  have hcomp : B.comp (symmetricSquareQuotient V) =
      (symmetricBilinearDescend β hβ).comp (symmetricSquareQuotient V) := by
    apply TensorProduct.ext'
    intro v w
    change B (symmetricSquareProduct V v w) =
      symmetricBilinearDescend β hβ (symmetricSquareProduct V v w)
    rw [hB, symmetricBilinearDescend_product]
  apply LinearMap.ext
  intro z
  induction z using Submodule.Quotient.induction_on with
  | _ t => exact congrArg (fun L : V ⊗[ℝ] V →ₗ[ℝ] W ↦ L t) hcomp

end GlobalEmbedding.Paper
