import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import GlobalEmbedding.Paper.SymmetricSquareNorms
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Exact pairings in the original Hilbert symmetric-square quotient

Source: original `prop:supported-rank`, lines 1007–1022, and normalized product
at 1129–1130. DAG: `symmetric-square-hilbert-pairing`. Exclusive worker W2.
All inner products below use Mathlib's native closed-quotient inner product,
which induces the existing Hilbert tensor quotient norm. No operator norm is transported.
-/

noncomputable section
open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

local instance pairingSquareRelationsClosed :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

local instance pairingSquareNormed : NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

omit [FiniteDimensional ℝ V] in
/-- The normalized symmetric tensor lies in the literal relation orthogonal complement.
Source: the original normalized half-sum convention. -/
theorem symmetricTensor_mem_relations_orthogonal (v w : V) :
    (1 / 2 : ℝ) • (v ⊗ₜ[ℝ] w + w ⊗ₜ[ℝ] v) ∈
      (symmetricSquareRelations V)ᗮ := by
  have hle : symmetricSquareRelations V ≤
      (innerₗ (V ⊗[ℝ] V) ((1 / 2 : ℝ) • (v ⊗ₜ[ℝ] w + w ⊗ₜ[ℝ] v))).ker := by
    apply Submodule.span_le.mpr
    rintro _ ⟨⟨x, y⟩, rfl⟩
    change inner ℝ ((1 / 2 : ℝ) • (v ⊗ₜ[ℝ] w + w ⊗ₜ[ℝ] v))
      (x ⊗ₜ[ℝ] y - y ⊗ₜ[ℝ] x) = 0
    simp only [TensorProduct.inner_def]
    simp
    ring
  rw [Submodule.mem_orthogonal']
  intro z hz
  exact hle hz

omit [FiniteDimensional ℝ V] in
private theorem symmetricTensor_quotient_eq_product (v w : V) :
    Submodule.Quotient.mk
        ((1 / 2 : ℝ) • (v ⊗ₜ[ℝ] w + w ⊗ₜ[ℝ] v)) =
      symmetricSquareProduct V v w := by
  change (symmetricSquareQuotient V)
    ((1 / 2 : ℝ) • (v ⊗ₜ[ℝ] w + w ⊗ₜ[ℝ] v)) = _
  rw [map_smul, map_add]
  change (1 / 2 : ℝ) • (symmetricSquareProduct V v w +
    symmetricSquareProduct V w v) = symmetricSquareProduct V v w
  rw [symmetricSquareProduct_comm V w v, ← two_smul ℝ (symmetricSquareProduct V v w),
    smul_smul]
  norm_num

/-- Exact product pairing in the SAME quotient inner product, including the half.
Source: normalized product in the original legal-normal computation. -/
theorem symmetricSquare_inner_product_product (v w x y : V) :
    inner ℝ (symmetricSquareProduct V v w) (symmetricSquareProduct V x y) =
      (1 / 2 : ℝ) *
        (inner ℝ v x * inner ℝ w y + inner ℝ v y * inner ℝ w x) := by
  rw [← symmetricTensor_quotient_eq_product v w, ← symmetricTensor_quotient_eq_product x y]
  rw [Submodule.Quotient.inner_mk_mk (symmetricSquareRelations V) _ _
    (symmetricTensor_mem_relations_orthogonal v w)
    (symmetricTensor_mem_relations_orthogonal x y)]
  simp only [TensorProduct.inner_def]
  simp
  ring

/-- Pairing with a product is evaluation of the SAME actual self-adjoint operator.
Source: legal normals `e ⊙ ξ` and quadratic evaluation in `prop:supported-rank`. -/
theorem symmetricSquare_inner_product_eq_operator (q : SymmetricSquare V) (v w : V) :
    inner ℝ q (symmetricSquareProduct V v w) =
      inner ℝ ((symmetricSquareToSelfAdjoint q).val v) w := by
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul x y =>
      change inner ℝ (symmetricSquareProduct V x y) (symmetricSquareProduct V v w) =
        inner ℝ ((symmetricSquareToSelfAdjoint (symmetricSquareProduct V x y)).val v) w
      rw [symmetricSquare_inner_product_product, symmetricSquareToSelfAdjoint_product]
      simp only [real_inner_smul_left, inner_add_left]
      ring
    | add t u ht hu =>
      change inner ℝ (symmetricSquareQuotient V (t + u))
          (symmetricSquareProduct V v w) =
        inner ℝ ((symmetricSquareToSelfAdjoint
          (symmetricSquareQuotient V (t + u))).val v) w
      simp only [map_add, inner_add_left, AddSubgroup.coe_add, add_apply]
      exact congrArg₂ (· + ·) ht hu

end GlobalEmbedding.Paper
