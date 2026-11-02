import GlobalEmbedding.Paper.TensorContractionRelations
import GlobalEmbedding.Paper.SymmetricSquare

/-!
# Contraction on the binary symmetric-square quotient

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, where the true second form is regarded as a linear map on `Sym²`, and Proposition
`prop:saturation`, lines 948–953 and 971–983, which uses the contraction notation `Pξ`.
The quotient model is the explicit binary tensor quotient of DAG node
`immersion-symmetric-square`. This module factors the tensor contraction of
`contraction-kernel-tensor-map` through that quotient using the proved relation-annihilation
result `contraction-kernel-tensor-map-kills-relations`. The value on the quotient class of
`v ⊗ w` is the prescribed half-sum. This module does not identify that class with the paper's
normalized symmetric tensor without a separate equivalence.
-/

namespace GlobalEmbedding.Paper

open scoped TensorProduct

/-- The linear contraction induced on the explicit binary symmetric-square quotient.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, and Proposition `prop:saturation`, lines 948–953 and 971–983. The map is the
quotient lift of `contractionKernelTensorMap`; its well-definedness uses
`contractionKernelTensorMap_killsRelations` and the quotient universal property. The quotient
class of `v ⊗ₜ w` is sent to `(ξ v • w + ξ w • v)/2`, without asserting an identification with
the normalized tensor representative in the paper's notation.
-/
noncomputable def contractionKernelQuotientMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) : SymmetricSquare V →ₗ[ℝ] V :=
  (symmetricSquareRelations V).liftQ (contractionKernelTensorMap ξ)
    (contractionKernelTensorMap_killsRelations ξ)

/-- The quotient contraction evaluates on the canonical product by the prescribed half-sum.

Source: the formula used by Proposition `prop:saturation`,
`literature/parallelizable-stable-plus-one/main.tex`, lines 948–953 and 971–983, interpreted
in the explicit quotient model of DAG node `immersion-symmetric-square`.
-/
@[simp]
theorem contractionKernelQuotientMap_product {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) (v w : V) :
    contractionKernelQuotientMap ξ (symmetricSquareProduct V v w) =
      (1 / 2 : ℝ) • (ξ v • w + ξ w • v) := by
  rw [symmetricSquareProduct_apply, contractionKernelQuotientMap]
  simp [symmetricSquareQuotient]

end GlobalEmbedding.Paper
