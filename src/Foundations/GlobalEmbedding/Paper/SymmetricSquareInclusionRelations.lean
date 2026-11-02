import GlobalEmbedding.Paper.SymmetricSquare
import Mathlib.LinearAlgebra.TensorProduct.Map

/-!
# The tensor inclusion preserves symmetric-square relations

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, where the second form is regarded on `Sym²`; the explicit binary quotient is the
model in DAG node `immersion-symmetric-square`. The paper uses this functorial symmetric-square
construction in Proposition `prop:saturation`, lines 948–953 and 971–983, without detailing its
quotient map. This lemma verifies directly that the tensor map induced by `ker ξ ↪ V` takes the
antisymmetric relation submodule into the ambient antisymmetric relation submodule.
-/

namespace GlobalEmbedding.Paper

open scoped TensorProduct

/-- The tensor map from `ker ξ` into `V` preserves the antisymmetric relation submodules.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 205, and Proposition `prop:saturation`, lines 948–953 and 971–983. This is the explicit
quotient well-definedness step for the inclusion of binary symmetric squares used in the
paper's restriction `Sym² ker ξ → Sym² V`; the proof maps each defining antisymmetric generator
to the corresponding ambient generator.
-/
theorem contractionKernelInclusion_preservesRelations {V : Type*} [AddCommGroup V]
    [Module ℝ V] (ξ : V →ₗ[ℝ] ℝ) :
    (symmetricSquareRelations (LinearMap.ker ξ)).map
      (TensorProduct.map (LinearMap.ker ξ).subtype (LinearMap.ker ξ).subtype) ≤
        symmetricSquareRelations V := by
  let H := LinearMap.ker ξ
  let j : H →ₗ[ℝ] V := H.subtype
  change (symmetricSquareRelations H).map (TensorProduct.map j j) ≤
    symmetricSquareRelations V
  rw [Submodule.map_le_iff_le_comap, symmetricSquareRelations, symmetricSquareRelations]
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨h, k⟩, rfl⟩
  change TensorProduct.map j j (h ⊗ₜ[ℝ] k - k ⊗ₜ[ℝ] h) ∈
    symmetricSquareRelations V
  rw [map_sub, TensorProduct.map_tmul, TensorProduct.map_tmul]
  exact Submodule.subset_span ⟨(j h, j k), rfl⟩

end GlobalEmbedding.Paper
