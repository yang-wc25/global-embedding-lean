import GlobalEmbedding.Paper.TensorContraction
import GlobalEmbedding.Paper.SymmetricSquare

/-!
# Antisymmetric relations are killed by the tensor contraction

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, which puts the true second form on `Sym²`, and Proposition `prop:saturation`,
lines 948–953 and 971–983, which uses the contraction notation `Pξ`. In the explicit binary
quotient model of DAG node `immersion-symmetric-square`, this lemma verifies the relation-killing
condition needed to factor the tensor map of DAG node `contraction-kernel-tensor-map` through
that quotient. The calculation uses the exact half-sum from
`contraction-kernel-tensor-contraction`.
-/

namespace GlobalEmbedding.Paper

open scoped TensorProduct

/-- The tensor contraction vanishes on the span of the antisymmetric generators.

Source: the quotient model of `Sym²` formalizing the domain in Definition `defn:phase`,
`literature/parallelizable-stable-plus-one/main.tex`, line 205, together with the contraction
notation in Proposition `prop:saturation`, lines 948–953 and 971–983. This is the exact
relation-killing obligation for the quotient factorization in DAG node
`contraction-kernel-tensor-map-kills-relations`; each generator is killed because the
half-sum from `contraction-kernel-tensor-contraction` is symmetric in its arguments.
-/
theorem contractionKernelTensorMap_killsRelations {V : Type*} [AddCommGroup V]
    [Module ℝ V] (ξ : V →ₗ[ℝ] ℝ) :
    symmetricSquareRelations V ≤ LinearMap.ker (contractionKernelTensorMap ξ) := by
  rw [symmetricSquareRelations]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨v, w⟩, rfl⟩
  change contractionKernelTensorMap ξ (v ⊗ₜ[ℝ] w - w ⊗ₜ[ℝ] v) = 0
  rw [map_sub, contractionKernelTensorMap_tmul, contractionKernelTensorMap_tmul]
  simp [add_comm]

end GlobalEmbedding.Paper
