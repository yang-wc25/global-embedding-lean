import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.Projection.FiniteDimensional
import Mathlib.Tactic.Module

/-!+# A genuine original-tensor evaluation right inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1012. The normalized quotient tensor `2(e⊙v)-⟨e,v⟩(e⊙e)` acts on a unit `e` as `v`.
Projection to an actual kernel complement preserves this evaluation whenever that kernel
annihilates `e`. These are actual algebraic inputs to the local defining submersion.
-/

noncomputable section

namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The actual original binary-quotient lift, including the exact half-sum normalization.
Source: `prop:supported-rank`, prescribed variation at the common radical. -/
def supportedRadicalEvaluationLift (e : V) : V →ₗ[ℝ] SymmetricSquare V :=
  (2 : ℝ) • symmetricSquareProduct V e -
    (innerₗ V e).smulRight (symmetricSquareProduct V e e)

/-- The original tensor lift is an actual right inverse of evaluation at a unit radical.
Source: `prop:supported-rank`, local normal-submersion construction. -/
theorem supportedRadicalEvaluationLift_apply (e : V) (he : ‖e‖ = 1) (v : V) :
    (symmetricSquareToSelfAdjoint (supportedRadicalEvaluationLift e v)).val e = v := by
  change (symmetricSquareToSelfAdjoint ((2 : ℝ) • symmetricSquareProduct V e v -
    inner ℝ e v • symmetricSquareProduct V e e)).val e = v
  rw [map_sub, map_smul, map_smul]
  change (2 : ℝ) • (symmetricSquareToSelfAdjoint (symmetricSquareProduct V e v)).val e -
    inner ℝ e v • (symmetricSquareToSelfAdjoint (symmetricSquareProduct V e e)).val e = v
  rw [symmetricSquareToSelfAdjoint_product, symmetricSquareToSelfAdjoint_product]
  simp [he, real_inner_comm, smul_add, smul_smul]
  module

omit [FiniteDimensional ℝ V] in
/-- Projecting a genuine evaluation right inverse to the original kernel complement
preserves it, because the removed kernel part has zero evaluation.
Source: `prop:supported-rank`, onto normal differential in actual kernel graph coordinates. -/
theorem supportedRadicalComplement_evaluation_lift
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]
    (K : Submodule ℝ H) (E : H →ₗ[ℝ] V) (L : V →ₗ[ℝ] H)
    (hK : ∀ q ∈ K, E q = 0) (hL : ∀ v, E (L v) = v) (v : V) :
    E (Kᗮ.starProjection (L v)) = v := by
  rw [Submodule.starProjection_orthogonal]
  change E (L v - K.starProjection (L v)) = v
  have hproj : K.starProjection (L v) ∈ K :=
    (K.orthogonalProjectionOnto (L v)).property
  rw [map_sub, hL, hK _ hproj, sub_zero]

end GlobalEmbedding.Paper
