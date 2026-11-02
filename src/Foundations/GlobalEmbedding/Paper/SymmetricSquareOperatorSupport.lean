import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation
import GlobalEmbedding.Paper.QuadraticSpaceKernelSupport

/-!
# The actual binary quotient support equals operator range support

Source: original `prop:saturation`, lines 990–995, and `prop:supported-rank`,
lines 1005–1022. DAG: `symmetric-square-operator-support`. Exclusive worker W2.
The accepted W1 orthogonal-kernel result is reused, with the same quotient/CLE.
-/

noncomputable section
open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F]

/-- The exact symmetric-square transport acts by actual adjoint conjugation.
Source: tensor/operator dictionary in the original saturation argument. -/
theorem symmetricSquareToSelfAdjoint_map_apply (f : E →L[ℝ] F)
    (q : SymmetricSquare E) (x : F) :
    (symmetricSquareToSelfAdjoint (symmetricSquareLinearMap f.toLinearMap q)).val x =
      f ((symmetricSquareToSelfAdjoint q).val (f.adjoint x)) := by
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w =>
      change (symmetricSquareToSelfAdjoint
        (symmetricSquareLinearMap f.toLinearMap (symmetricSquareProduct E v w))).val x =
          f ((symmetricSquareToSelfAdjoint (symmetricSquareProduct E v w)).val
            (f.adjoint x))
      have hp := symmetricBilinearDescend_product
        (((symmetricSquareProduct F).compl₂ f.toLinearMap).comp f.toLinearMap)
        (fun v w ↦ symmetricSquareProduct_comm F (f v) (f w)) v w
      change symmetricSquareLinearMap f.toLinearMap (symmetricSquareProduct E v w) =
        symmetricSquareProduct F (f v) (f w) at hp
      rw [hp, symmetricSquareToSelfAdjoint_product, symmetricSquareToSelfAdjoint_product]
      simp [ContinuousLinearMap.adjoint_inner_right]
    | add t u ht hu =>
      change (symmetricSquareToSelfAdjoint
        (symmetricSquareLinearMap f.toLinearMap
          (symmetricSquareQuotient E (t + u)))).val x =
            f ((symmetricSquareToSelfAdjoint (symmetricSquareQuotient E (t + u))).val
              (f.adjoint x))
      simp only [map_add, AddSubgroup.coe_add, add_apply]
      exact congrArg₂ (· + ·) ht hu

/-- An actual quotient tensor is supported on U exactly when its actual
self-adjoint operator has range in U. Source: `prop:saturation`, support classification.

Proof: inclusion acts by adjoint conjugation. Conversely project q to Sym²U,
include it back, and use the accepted self-adjoint kills-orthogonal result to show
that the same operator is unchanged. Injectivity of the actual equivalence recovers q.
No desired support identity or isometry is an input. -/
theorem symmetricSquare_mem_range_iff_operator_range (U : Submodule ℝ E)
    (q : SymmetricSquare E) :
    q ∈ LinearMap.range (symmetricSquareLinearMap U.subtype) ↔
      LinearMap.range (symmetricSquareToSelfAdjoint q).val.toLinearMap ≤ U := by
  constructor
  · rintro ⟨r, rfl⟩ y ⟨x, rfl⟩
    have h := symmetricSquareToSelfAdjoint_map_apply U.subtypeL r x
    change (symmetricSquareToSelfAdjoint
      (symmetricSquareLinearMap U.subtypeL.toLinearMap r)).val x ∈ U
    rw [h]
    exact Submodule.coe_mem _
  · intro hq
    let r := symmetricSquareLinearMap U.orthogonalProjectionOnto.toLinearMap q
    refine ⟨r, ?_⟩
    apply symmetricSquareSelfAdjointEquiv.injective
    apply Subtype.ext
    ext x
    change (symmetricSquareToSelfAdjoint
      (symmetricSquareLinearMap U.subtypeL.toLinearMap r)).val x =
      (symmetricSquareToSelfAdjoint q).val x
    rw [symmetricSquareToSelfAdjoint_map_apply U.subtypeL r x]
    change U.subtypeL
      ((symmetricSquareToSelfAdjoint
        (symmetricSquareLinearMap U.orthogonalProjectionOnto.toLinearMap q)).val
          (U.subtypeL.adjoint x)) = _
    rw [symmetricSquareToSelfAdjoint_map_apply, U.adjoint_subtypeL,
      U.adjoint_orthogonalProjectionOnto]
    change U.starProjection
      ((symmetricSquareToSelfAdjoint q).val (U.starProjection x)) =
        (symmetricSquareToSelfAdjoint q).val x
    have hm : (symmetricSquareToSelfAdjoint q).val (U.starProjection x) ∈ U :=
      hq ⟨U.starProjection x, rfl⟩
    rw [U.starProjection_eq_self_iff.mpr hm]
    have hz := quadraticSpace_kills_orthogonal
      (symmetricSquareToSelfAdjoint q).val
      (symmetricSquareToSelfAdjoint q).property.isSymmetric U hq
      (U.sub_starProjection_mem_orthogonal x)
    exact (sub_eq_zero.mp (by simpa only [map_sub] using hz)).symm

/-- Subspace support is the same actual pointwise operator-range condition.
Source: supported K in the original saturation and legal-rank statements. -/
theorem symmetricSquare_submodule_supported_iff (K : Submodule ℝ (SymmetricSquare E))
    (U : Submodule ℝ E) :
    K ≤ LinearMap.range (symmetricSquareLinearMap U.subtype) ↔
      ∀ q ∈ K, LinearMap.range (symmetricSquareToSelfAdjoint q).val.toLinearMap ≤ U := by
  constructor
  · intro h q hq
    exact (symmetricSquare_mem_range_iff_operator_range U q).mp (h hq)
  · intro h q hq
    exact (symmetricSquare_mem_range_iff_operator_range U q).mpr (h q hq)

end GlobalEmbedding.Paper
