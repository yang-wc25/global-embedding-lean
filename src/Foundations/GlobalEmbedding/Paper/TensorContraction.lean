import Mathlib.LinearAlgebra.TensorProduct.Basic
import GlobalEmbedding.Paper.BilinearContraction

/-!
# Tensor extension of the symmetric contraction

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, where the true second form is treated as a map on `Sym²`, and Proposition
`prop:saturation`, lines 948–953 and 971–983, where the contraction `Pξ` is used. This module
extends the explicit bilinear map from DAG node `contraction-kernel-tensor-contraction` to
`V ⊗[ℝ] V` by the tensor-product universal property. The output on `v ⊗ₜ w` retains the exact
factor `1/2` in that node's definition. No quotient map or relation-killing claim is made here.
-/

namespace GlobalEmbedding.Paper

open scoped TensorProduct

/-- The linear map on `V ⊗[ℝ] V` induced by the bilinear contraction `contractionKernelBeta`.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, and Proposition `prop:saturation`, lines 948–953 and 971–983. The construction uses
the tensor-product universal property on the explicit half-sum from DAG node
`contraction-kernel-tensor-contraction`; it does not yet factor through the symmetric-square
quotient.
-/
noncomputable def contractionKernelTensorMap {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) : (V ⊗[ℝ] V) →ₗ[ℝ] V :=
  TensorProduct.lift (contractionKernelBeta ξ)

/-- On a pure tensor, the tensor extension evaluates to the specified half-sum.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, and Proposition `prop:saturation`, lines 948–953 and 971–983; the bilinear formula
is specified by DAG node `contraction-kernel-tensor-contraction`.
-/
@[simp]
theorem contractionKernelTensorMap_tmul {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) (v w : V) :
    contractionKernelTensorMap ξ (v ⊗ₜ[ℝ] w) =
      (1 / 2 : ℝ) • (ξ v • w + ξ w • v) := by
  rw [contractionKernelTensorMap, TensorProduct.lift.tmul, contractionKernelBeta_apply]

end GlobalEmbedding.Paper
