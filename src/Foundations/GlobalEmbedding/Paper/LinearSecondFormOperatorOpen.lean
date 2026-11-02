import GlobalEmbedding.Paper.SupportedLocusLocalEquations
import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# Openness in the original second-form operator ambient

Source: original `prop:supported-rank`, lines 998–1006.
DAG: `linear-second-form-operator-phase-open`. Exclusive worker W2.
The quotient, quotient norm and sole actual Good/phase predicates are unchanged.
-/

noncomputable section
namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed

/-- For a fixed actual covector, Good is open in the original operator B.
Proof: use finite coordinates of the literal Sym² ker ξ only internally. Restriction
of the actual B is continuous by native operator composition, and injectivity is open.
Source: the original onto/phase ambient in `prop:supported-rank`. -/
theorem isOpen_linearSecondFormGoodCovector_operator
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] (ξ : V →ₗ[ℝ] ℝ) :
    IsOpen {B : SymmetricSquare V →L[ℝ] W |
      LinearSecondFormGoodCovector B.toLinearMap ξ} := by
  by_cases hξ : ξ = 0
  · simp [hξ, LinearSecondFormGoodCovector]
  let S := SymmetricSquare ξ.ker
  let C := Fin (Module.finrank ℝ S) → ℝ
  let e : S ≃ₗ[ℝ] C := (Module.finBasis ℝ S).equivFun
  let j : C →L[ℝ] SymmetricSquare V :=
    ((symmetricSquareLinearMap ξ.ker.subtype).comp e.symm.toLinearMap).toContinuousLinearMap
  let A : (SymmetricSquare V →L[ℝ] W) →L[ℝ] (C →L[ℝ] W) :=
    (ContinuousLinearMap.compL ℝ C (SymmetricSquare V) W).flip j
  have hi (B : SymmetricSquare V →L[ℝ] W) :
      Function.Injective (B.toLinearMap.comp (symmetricSquareLinearMap ξ.ker.subtype)) ↔
        Function.Injective (A B) := by
    constructor
    · intro h u v huv
      have heq : e.symm u = e.symm v := h huv
      exact e.symm.injective heq
    · intro h u v huv
      apply e.injective
      apply h
      change B (symmetricSquareLinearMap ξ.ker.subtype (e.symm (e u))) =
        B (symmetricSquareLinearMap ξ.ker.subtype (e.symm (e v)))
      change B (symmetricSquareLinearMap ξ.ker.subtype u) =
        B (symmetricSquareLinearMap ξ.ker.subtype v) at huv
      simpa only [e.symm_apply_apply] using huv
  have heq : {B : SymmetricSquare V →L[ℝ] W |
      LinearSecondFormGoodCovector B.toLinearMap ξ} =
        {B | Function.Injective (A B)} := by
    ext B
    simp only [Set.mem_ofPred_eq, LinearSecondFormGoodCovector, hξ, ne_eq,
      not_false_eq_true, true_and, hi]
  rw [heq]
  exact ContinuousLinearMap.isOpen_injective.preimage A.continuous

/-- Existence of an actual good covector is open in the FULL original operator space.
Source: the phase-regular ambient of original `prop:supported-rank`.
Proof: take the union of the proved fixed-covector open sets over all actual covectors. -/
theorem isOpen_linearSecondFormPhaseRegular_operator
    {W : Type*} [NormedAddCommGroup W] [NormedSpace ℝ W] :
    IsOpen {B : SymmetricSquare V →L[ℝ] W |
      LinearSecondFormPhaseRegular B.toLinearMap} := by
  change IsOpen {B : SymmetricSquare V →L[ℝ] W |
    ∃ ξ : V →ₗ[ℝ] ℝ, LinearSecondFormGoodCovector B.toLinearMap ξ}
  simp only [Set.ofPred_exists]
  exact isOpen_iUnion fun ξ ↦ isOpen_linearSecondFormGoodCovector_operator ξ

/-- The exact onto AND phase-regular ambient of original `prop:supported-rank` is open.
Proof: the native continuous adjoint turns onto into injectivity by orthogonal range
duality, so native injective openness applies. Intersect with the proved phase-open set.
The inner product on the original quotient is the native quotient inner product with
its already fixed canonical norm; no operator-model norm is transported. -/
theorem isOpen_surjective_linearSecondFormPhaseRegular
    {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W]
    [FiniteDimensional ℝ W] :
    IsOpen {B : SymmetricSquare V →L[ℝ] W |
      Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap} := by
  let : InnerProductSpace ℝ (SymmetricSquare V) :=
    { Submodule.instQuotientInnerProductSpace (symmetricSquareRelations V) with
      toNormedSpace := squareNS V }
  have hs : IsOpen {B : SymmetricSquare V →L[ℝ] W | Function.Surjective B} := by
    have heq : {B : SymmetricSquare V →L[ℝ] W | Function.Surjective B} =
        {B | Function.Injective (ContinuousLinearMap.adjoint B)} := by
      ext B
      change Function.Surjective B.toLinearMap ↔
        Function.Injective (ContinuousLinearMap.adjoint B).toLinearMap
      rw [← LinearMap.range_eq_top, ← LinearMap.ker_eq_bot,
        ← B.orthogonal_range, Submodule.orthogonal_eq_bot_iff]
    rw [heq]
    exact ContinuousLinearMap.isOpen_injective.preimage
      ContinuousLinearMap.adjoint.continuous
  exact hs.inter isOpen_linearSecondFormPhaseRegular_operator

end GlobalEmbedding.Paper
