import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import Mathlib.Tactic.Module

/-!
# Evaluation on the actual mixed product range is injective

Source: original `prop:supported-rank`, lines 1007–1022 and product convention
1129–1130. DAG: `supported-rank-mixed-contraction`. Exclusive worker W2.
The actual contraction restricted to Z=e⊙V is used, with its explicit half factor.
This does not rebuild W6's vector-to-mixed-range equivalence or lifted-span proof.
-/

namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- Evaluation of the same original contraction on the actual mixed product.
Source: normalized mixed columns of the original supported-kernel proof. -/
theorem symmetricSquare_mixed_contraction (e : V) (he : inner ℝ e e = 1) (v : V) :
    contractionKernelQuotientMap (innerₗ V e) (symmetricSquareProduct V e v) =
      (1 / 2 : ℝ) • (v + inner ℝ e v • e) := by
  rw [contractionKernelQuotientMap_product]
  simp only [innerₗ_apply_apply, he, one_smul]

/-- The explicit recovery from actual mixed evaluation preserves the diagonal factor.
Source: actual evaluation Z→V in the original normal quotient calculation. -/
theorem symmetricSquare_mixed_recover (e : V) (he : inner ℝ e e = 1) (v : V) :
    (2 : ℝ) • contractionKernelQuotientMap (innerₗ V e) (symmetricSquareProduct V e v) -
      inner ℝ e
        (contractionKernelQuotientMap (innerₗ V e) (symmetricSquareProduct V e v)) • e = v := by
  rw [symmetricSquare_mixed_contraction e he v]
  have hi : inner ℝ e ((1 / 2 : ℝ) • (v + inner ℝ e v • e)) = inner ℝ e v := by
    simp only [real_inner_smul_right, inner_add_right, he]
    ring
  rw [hi]
  module

/-- The SAME contraction, restricted to the literal actual mixed range, is injective.
Source: determination of the normal-quotient kernel from its recovered support derivative. -/
theorem symmetricSquare_mixed_contraction_injective (e : V) (he : inner ℝ e e = 1) :
    Function.Injective ((contractionKernelQuotientMap (innerₗ V e)).domRestrict
      (LinearMap.range (symmetricSquareProduct V e))) := by
  let Z := LinearMap.range (symmetricSquareProduct V e)
  have hrec (q : Z) :
      symmetricSquareProduct V e
        ((2 : ℝ) • contractionKernelQuotientMap (innerₗ V e) q.val -
          inner ℝ e (contractionKernelQuotientMap (innerₗ V e) q.val) • e) = q.val := by
    obtain ⟨v, hv⟩ := q.property
    rw [← hv, symmetricSquare_mixed_recover e he v]
  intro q r hqr
  change contractionKernelQuotientMap (innerₗ V e) q.val =
    contractionKernelQuotientMap (innerₗ V e) r.val at hqr
  apply Subtype.ext
  rw [← hrec q, ← hrec r, hqr]

/-- The actual self-adjoint operator evaluation at e is injective on the SAME Z.
Source: the operator dictionary consumed by the original supported-locus chart. -/
theorem symmetricSquare_mixed_operator_evaluation_injective
    [FiniteDimensional ℝ V] (e : V) (he : inner ℝ e e = 1) :
    Function.Injective (fun q : LinearMap.range (symmetricSquareProduct V e) ↦
      (symmetricSquareToSelfAdjoint q.val).val e) := by
  intro q r hqr
  apply symmetricSquare_mixed_contraction_injective e he
  change contractionKernelQuotientMap (innerₗ V e) q.val =
    contractionKernelQuotientMap (innerₗ V e) r.val
  simpa only [symmetricSquareToSelfAdjoint_apply] using hqr

end GlobalEmbedding.Paper
