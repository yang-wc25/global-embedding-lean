import GlobalEmbedding.Paper.SymmetricSquareInclusionRelations
import GlobalEmbedding.Paper.SymmetricSquare

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition
`defn:phase` and Proposition `prop:saturation`. The map is the inclusion of the symmetric
square of `ker ξ` into the ambient binary symmetric square. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

/-- The quotient map induced by the tensor-square of the subtype inclusion `ker ξ ↪ V`.
Source: `defn:phase`, line 205, and `prop:saturation`, lines 948–953 and 971–983. -/
noncomputable def contractionKernelSymmetricSquareInclusion {V : Type*} [AddCommGroup V]
    [Module ℝ V] (ξ : V →ₗ[ℝ] ℝ) :
    SymmetricSquare (LinearMap.ker ξ) →ₗ[ℝ] SymmetricSquare V :=
  (symmetricSquareRelations (LinearMap.ker ξ)).mapQ (symmetricSquareRelations V)
    (TensorProduct.map (LinearMap.ker ξ).subtype (LinearMap.ker ξ).subtype)
    (Submodule.map_le_iff_le_comap.mp (contractionKernelInclusion_preservesRelations ξ))

/-- The induced inclusion sends each quotient representative to the class of its tensor-map
image. -/
@[simp] theorem contractionKernelSymmetricSquareInclusion_mk {V : Type*}
    [AddCommGroup V] [Module ℝ V] (ξ : V →ₗ[ℝ] ℝ) (z :
      (LinearMap.ker ξ) ⊗[ℝ] (LinearMap.ker ξ)) :
    contractionKernelSymmetricSquareInclusion ξ (Submodule.Quotient.mk z) =
      Submodule.Quotient.mk
        (TensorProduct.map (LinearMap.ker ξ).subtype (LinearMap.ker ξ).subtype z) := by
  rw [contractionKernelSymmetricSquareInclusion]
  rfl

end GlobalEmbedding.Paper

#check GlobalEmbedding.Paper.contractionKernelSymmetricSquareInclusion
#check GlobalEmbedding.Paper.contractionKernelSymmetricSquareInclusion_mk
#print axioms GlobalEmbedding.Paper.contractionKernelSymmetricSquareInclusion
