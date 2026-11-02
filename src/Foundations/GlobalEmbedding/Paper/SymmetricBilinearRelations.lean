import GlobalEmbedding.Paper.SymmetricSquare

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, actual normal second form on the exact binary Sym² quotient. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {V W : Type*} [AddCommGroup V] [Module ℝ V] [AddCommGroup W] [Module ℝ W]

/-- The tensor lift of a symmetric bilinear map kills every antisymmetric relation.
Proof: each generator v⊗w−w⊗v maps to β(v,w)−β(w,v)=0, then use the span property.
Source: `defn:phase`, descent of the normal second form to Sym². -/
theorem symmetricBilinear_killsRelations (β : V →ₗ[ℝ] V →ₗ[ℝ] W)
    (hβ : ∀ v w, β v w = β w v) :
    symmetricSquareRelations V ≤ LinearMap.ker (TensorProduct.lift β) := by
  rw [symmetricSquareRelations]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨v, w⟩, rfl⟩
  change (TensorProduct.lift β) (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) = 0
  rw [map_sub, TensorProduct.lift.tmul, TensorProduct.lift.tmul, hβ v w, sub_self]

end GlobalEmbedding.Paper
