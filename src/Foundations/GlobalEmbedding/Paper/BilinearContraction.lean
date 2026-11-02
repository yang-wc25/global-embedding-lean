import Mathlib.LinearAlgebra.BilinearMap
import Mathlib.Basic.Real.Basic

/-!
# The bilinear contraction underlying the symmetric-square map

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, where the second form is regarded as a linear map on `Sym²`, and Proposition
`prop:saturation`, lines 948–953 and 971–983, where contraction notation `Pξ` is used.
The contraction formula is formalized as the real bilinear map specified by DAG node
`contraction-kernel-tensor-contraction`. Its factor `1/2` is explicit; the quotient class
of `v ⊗ w` and the paper's normalized tensor `(v ⊗ w + w ⊗ v)/2` are not identified here.
The definition works for any real module and makes no finite-dimensionality assumption.
-/

namespace GlobalEmbedding.Paper

noncomputable section

/-- The symmetric bilinear contraction formula on a real module.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, and Proposition `prop:saturation`, lines 948–953 and 971–983. This is the
bilinear map underlying the quotient contraction of DAG node
`contraction-kernel-tensor-contraction`; the factor `1/2` is part of its definition.
-/
def contractionKernelBeta {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) : V →ₗ[ℝ] V →ₗ[ℝ] V where
  toFun v :=
    { toFun := fun w ↦ (1 / 2 : ℝ) • (ξ v • w + ξ w • v)
      map_add' := by
        intro w₁ w₂
        simp [add_smul, smul_add]
        simp [add_assoc, add_left_comm]
      map_smul' := by
        intro c w
        simp [smul_add, smul_smul, mul_comm, mul_left_comm] }
  map_add' := by
    intro v₁ v₂
    ext w
    simp [add_smul, smul_add]
    simp [add_assoc, add_left_comm]
  map_smul' := by
    intro c v
    ext w
    simp [smul_add, smul_smul, mul_comm, mul_left_comm]

/-- The contraction's value on a pair is the stated half-sum.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, and Proposition `prop:saturation`, lines 948–953 and 971–983; see the
quotient-contraction formula recorded in DAG node `good-kernel-contraction`.
-/
@[simp]
theorem contractionKernelBeta_apply {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) (v w : V) :
    contractionKernelBeta ξ v w = (1 / 2 : ℝ) • (ξ v • w + ξ w • v) := rfl

/-- The bilinear contraction is symmetric in its two vector arguments.

Source: the contraction formula implicit in the good-covector discussion of Proposition
`prop:saturation`, `literature/parallelizable-stable-plus-one/main.tex`, lines 948–953 and
971–983; symmetry follows directly by swapping its two summands.
-/
theorem contractionKernelBeta_comm {V : Type*} [AddCommGroup V] [Module ℝ V]
    (ξ : V →ₗ[ℝ] ℝ) (v w : V) :
    contractionKernelBeta ξ v w = contractionKernelBeta ξ w v := by
  simp [add_comm]

end

end GlobalEmbedding.Paper
