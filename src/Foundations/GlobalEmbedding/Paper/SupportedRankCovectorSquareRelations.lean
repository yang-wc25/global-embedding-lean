import GlobalEmbedding.Paper.SymmetricSquare
import Mathlib.LinearAlgebra.TensorProduct.Associator

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:supported-rank`, covector-square evaluation in the kernel-variation argument. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

/-- The tensor-product linear map induced by the bilinear form
`(v, w) ↦ ξ v * ξ w`.
Source: `prop:supported-rank`, equation (9.4) and the evaluation `ξ²(Q)=Q(ξ,ξ)`. -/
def supportedRankCovectorSquareTensorMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) : V ⊗[ℝ] V →ₗ[ℝ] ℝ :=
  (TensorProduct.lid ℝ ℝ).toLinearMap.comp (TensorProduct.map ξ ξ)

/-- On pure tensors the map evaluates to `ξ v * ξ w`. -/
@[simp] theorem supportedRankCovectorSquareTensorMap_tmul {V : Type*} [AddCommGroup V]
    [Module ℝ V] (ξ : V →ₗ[ℝ] ℝ) (v w : V) :
    supportedRankCovectorSquareTensorMap ξ (v ⊗ₜ[ℝ] w) = ξ v * ξ w := by
  simp [supportedRankCovectorSquareTensorMap, TensorProduct.lid_tmul, smul_eq_mul]

/-- Covector-square evaluation kills every antisymmetric tensor and therefore their span.
Source: `prop:supported-rank`, equation (9.4), where `ξ²` evaluates a quadratic at `ξ`. -/
theorem supportedRankCovectorSquare_killsRelations {V : Type*} [AddCommGroup V]
    [Module ℝ V] (ξ : V →ₗ[ℝ] ℝ) :
    symmetricSquareRelations V ≤ LinearMap.ker (supportedRankCovectorSquareTensorMap ξ) := by
  rw [symmetricSquareRelations]
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨v, w⟩, rfl⟩
  change supportedRankCovectorSquareTensorMap ξ
    (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) = 0
  simp [supportedRankCovectorSquareTensorMap, mul_comm]

end GlobalEmbedding.Paper

#print GlobalEmbedding.Paper.supportedRankCovectorSquare_killsRelations
#print axioms GlobalEmbedding.Paper.supportedRankCovectorSquare_killsRelations
