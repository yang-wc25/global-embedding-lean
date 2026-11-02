import GlobalEmbedding.Paper.SymmetricBilinearDescendUnique

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- Every real symmetric bilinear map factors uniquely through the exact binary
symmetric-square quotient. No factor 1/2 occurs, including zero source/target spaces.
Proof: use the explicit canonical descent, its product formula and the uniqueness lemma.
Source: `defn:phase`, normal second form as a linear map on Sym². -/
theorem second_form_symmetric_quotient (β : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (hβ : ∀ v w, β v w = β w v) :
    ∃! B : SymmetricSquare V →ₗ[ℝ] W, ∀ v w,
      B (symmetricSquareProduct V v w) = β v w := by
  refine ⟨symmetricBilinearDescend β hβ, symmetricBilinearDescend_product β hβ, ?_⟩
  intro B hB
  exact symmetricBilinearDescend_unique β hβ B hB

end GlobalEmbedding.Paper
