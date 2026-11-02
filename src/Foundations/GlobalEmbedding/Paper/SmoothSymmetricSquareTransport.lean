import GlobalEmbedding.Paper.SymmetricSquareMapLEval
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance squareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance squareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The existing exact symmetric-square transport is smooth in its operator input,
using exactly the original finite Hilbert tensor quotient norms.

Proof: smoothness of a finite-domain operator field is equivalent to smoothness of
all its evaluations. Induct on an actual quotient representative and its tensor
decomposition. At a pure tensor, transport is the actual symmetric product of Av
and Aw, a bounded bilinear operation in these finite normed spaces. Sums preserve
smoothness. No quotient, map, norm or normalization is replaced.
Source: smooth symmetric-square chart transitions expanding `defn:phase`. -/
theorem smooth_symmetric_square_transport
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
    [FiniteDimensional ℝ F] {n : ℕ∞ω} :
    ContDiff ℝ n (fun A : E →L[ℝ] F ↦ symmetricSquareMapL A) := by
  let lift : (F →ₗ[ℝ] SymmetricSquare F) ≃ₗ[ℝ] F →L[ℝ] SymmetricSquare F :=
    LinearMap.toContinuousLinearMap
  let B : F →L[ℝ] F →L[ℝ] SymmetricSquare F :=
    LinearMap.toContinuousLinearMap (lift.toLinearMap.comp (symmetricSquareProduct F))
  apply contDiff_clm_apply_iff.mpr
  intro q
  induction q using Submodule.Quotient.induction_on with
  | _ t =>
    induction t using TensorProduct.inductionOn with
    | tmul v w =>
      have hv : ContDiff ℝ n (fun A : E →L[ℝ] F ↦ A v) :=
        contDiff_id.clm_apply contDiff_const
      have hw : ContDiff ℝ n (fun A : E →L[ℝ] F ↦ A w) :=
        contDiff_id.clm_apply contDiff_const
      have h := (B.contDiff.comp hv).clm_apply hw
      have heq : (fun A : E →L[ℝ] F ↦
          symmetricSquareMapL A (Submodule.Quotient.mk (v ⊗ₜ[ℝ] w))) =
          (fun A ↦ B (A v) (A w)) := by
        funext A
        simp [symmetricSquareMapL_apply, symmetricSquareMap,
          TensorProduct.map_tmul, B, lift, symmetricSquareProduct_apply]
        rfl
      rw [heq]
      exact h
    | add a b ha hb =>
      change ContDiff ℝ n (fun A : E →L[ℝ] F ↦
        symmetricSquareMapL A (symmetricSquareQuotient E (a + b)))
      simpa only [map_add, symmetricSquareQuotient, Submodule.mkQ_apply] using ha.add hb

end GlobalEmbedding.Paper
