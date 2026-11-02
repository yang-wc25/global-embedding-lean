import GlobalEmbedding.Paper.SupportedRankGoodEvaluationDual
import GlobalEmbedding.Paper.SupportedRadicalGraphChart
import GlobalEmbedding.Paper.SymmetricSquareMixedContraction
import Mathlib.Analysis.Normed.Module.Span

/-!+# The genuine good scalar block for the original supported kernel

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1006. Normalize the SOLE accepted good dual Jacobian by one half and use the
original operator dictionary in genuine finite coordinates. The actual scalar right block
is the identity; the left block vanishes because the original supported operators annihilate
the normal. No square-block or geometry assertion is supplied as an input.
-/

noncomputable section
open scoped TensorProduct

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [AddCommGroup W] [Module ℝ W]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] operatorSelfAdjointContinuousSMul

/-- Genuine finite coordinates for the orthogonal hyperplane of a nonzero local normal.
This reuses the native span equivalence and native orthogonal direct sum, with no isometry
claim or global orientation. Source: `prop:supported-rank`, `V=U⊕ℝe`. -/
def supportedRadicalOrthogonalCoordinates (e : V) (he : e ≠ 0) :
    (ℝ × (Submodule.span ℝ ({e} : Set V))ᗮ) ≃L[ℝ] V :=
  ((ContinuousLinearEquiv.toSpanNonzeroSingleton ℝ e he).prodCongr
    (ContinuousLinearEquiv.refl ℝ (Submodule.span ℝ ({e} : Set V))ᗮ)).trans
      (((Submodule.span ℝ ({e} : Set V)).prodEquivOfIsCompl
        (Submodule.span ℝ ({e} : Set V))ᗮ
        (Submodule.span ℝ ({e} : Set V)).isCompl_orthogonal).toContinuousLinearEquiv)

/-- The actual coordinate map is the literal sum `t*e+u`.
Source: `prop:supported-rank`, the original normal and supporting hyperplane coordinates. -/
theorem supportedRadicalOrthogonalCoordinates_apply (e : V) (he : e ≠ 0)
    (t : ℝ) (u : (Submodule.span ℝ ({e} : Set V))ᗮ) :
    supportedRadicalOrthogonalCoordinates e he (t, u) = t • e + (u : V) := rfl

/-- The actual scalar-row isomorphism is exactly one half of the accepted doubled dual J,
followed by native finite-dimensional dual continuity. Source: `prop:supported-rank`, scalar
tests rather than quadratic Hessians. The good E/J proof is reused, not repeated. -/
def supportedRadicalGoodRowEquiv (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) :
    U ≃L[ℝ] (B.ker →L[ℝ] ℝ) := by
  let A : U ≃ₗ[ℝ] (B.ker →L[ℝ] ℝ) :=
    ((supportedRankGoodKernelDualEquiv B U hK x hg hdim).trans
      (LinearEquiv.smulOfNeZero ℝ (Module.Dual ℝ B.ker) (1 / 2) (by norm_num))).trans
        (LinearMap.toContinuousLinearMap :
          Module.Dual ℝ B.ker ≃ₗ[ℝ] (B.ker →L[ℝ] ℝ))
  have : FiniteDimensional ℝ (B.ker →L[ℝ] ℝ) := A.finiteDimensional
  exact
    { toLinearEquiv := A
      continuous_toFun := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := U) (F' := B.ker →L[ℝ] ℝ) A.toLinearMap
      continuous_invFun := LinearMap.continuous_of_finiteDimensional
        (𝕜 := ℝ) (E := B.ker →L[ℝ] ℝ) (F' := U) A.symm.toLinearMap }

/-- The scalar row has the SAME original quadratic evaluation, with its factor two canceled.
Source: `prop:supported-rank`, actual row-block identity. -/
theorem supportedRadicalGoodRowEquiv_apply (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) (u : U) (k : B.ker) :
    supportedRadicalGoodRowEquiv B U hK x hg hdim u k =
      supportedRankKernelQuadratic B U k (U.orthogonalProjectionOnto x) u := by
  change (1 / 2 : ℝ) * supportedRankGoodKernelDualEquiv B U hK x hg hdim u k = _
  rw [supportedRankGoodKernelDualEquiv_apply]
  ring

/-- The SAME original quotient operator, in genuine finite local vector coordinates.
No product-norm isometry or transported norm is asserted.
Source: `prop:supported-rank`, actual local coordinates near a supporting hyperplane. -/
def supportedRadicalCoordinateOperatorMap (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V) :
    SymmetricSquare V →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)) :=
  (ContinuousLinearMap.compL ℝ (ℝ × U) V (ℝ × U) d.symm).comp
    (((ContinuousLinearMap.compL ℝ (ℝ × U) V V).flip d).comp
      ((selfAdjoint.submodule ℝ (V →L[ℝ] V)).subtypeL.comp
        symmetricSquareSelfAdjointCLE.toContinuousLinearMap))

/-- The actual coordinate operator evaluates to exactly the original operator in V.
Source: `prop:supported-rank`, literal kernel-operator family. -/
theorem supportedRadicalCoordinateOperatorMap_apply (U : Submodule ℝ V)
    (d : (ℝ × U) ≃L[ℝ] V) (q : SymmetricSquare V) (v : ℝ × U) :
    d (supportedRadicalCoordinateOperatorMap U d q v) =
      (symmetricSquareToSelfAdjoint q).val (d v) := by
  change d (d.symm ((symmetricSquareToSelfAdjoint q).val (d v))) = _
  exact d.apply_symm_apply _

/-- The actual mixed evaluation remains injective in these SAME local coordinates.
This only transports W2's sole original mixed-product theorem through the genuine CLE.
Source: `prop:supported-rank`, the actual same-chart support-motion kernel bound. -/
theorem supportedRadicalMixedCoordinate_evaluation_injective (U : Submodule ℝ V)
    (d : (ℝ × U) ≃L[ℝ] V) (e : V) (he : inner ℝ e e = 1) (hde : d (1, 0) = e) :
    Function.Injective (fun q : LinearMap.range (symmetricSquareProduct V e) ↦
      supportedRadicalCoordinateOperatorMap U d q.val (1, 0)) := by
  intro q q' h
  apply symmetricSquare_mixed_operator_evaluation_injective e he
  have hd := congrArg d h
  simpa only [supportedRadicalCoordinateOperatorMap_apply, hde] using hd

/-- The actual scalar test uses the original projected good vector and genuine coordinates.
Source: `prop:supported-rank`, the scalar equations recovering the common radical. -/
def supportedRadicalScalarTest (U : Submodule ℝ V) (x : V) (d : (ℝ × U) ≃L[ℝ] V) :
    (ℝ × U) →L[ℝ] ℝ :=
  (innerSL ℝ (U.orthogonalProjectionOnto x : V)).comp (d : (ℝ × U) →L[ℝ] V)

/-- The actual nonzero projected good vector supplies a genuine scalar section.
Source: `prop:supported-rank`, scalar-kernel normal-equation coordinates. -/
theorem supportedRadicalScalarTest_exists_section (U : Submodule ℝ V) (x : V)
    (d : (ℝ × U) ≃L[ℝ] V) (hz : U.orthogonalProjectionOnto x ≠ 0) :
    ∃ w : ℝ × U, supportedRadicalScalarTest U x d w = 1 := by
  have hzV : (U.orthogonalProjectionOnto x : V) ≠ 0 := by
    intro h
    exact hz (Subtype.ext h)
  refine ⟨d.symm ((‖(U.orthogonalProjectionOnto x : V)‖ ^ 2)⁻¹ •
    (U.orthogonalProjectionOnto x : V)), ?_⟩
  change inner ℝ (U.orthogonalProjectionOnto x : V)
    (d (d.symm ((‖(U.orthogonalProjectionOnto x : V)‖ ^ 2)⁻¹ •
      (U.orthogonalProjectionOnto x : V)))) = 1
  rw [d.apply_symm_apply, real_inner_smul_right, real_inner_self_eq_norm_sq]
  exact inv_mul_cancel₀ (pow_ne_zero 2 (norm_ne_zero_iff.mpr hzV))

/-- For the SAME supported kernel and SAME good vector, the actual scalar right block is
the identity, not a supplied invertibility premise. Source: `prop:supported-rank`, good block. -/
theorem supportedRadicalGoodRow_rightBlock (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) (d : (ℝ × U) ≃L[ℝ] V)
    (hdU : ∀ u : U, d (0, u) = (u : V)) :
    supportedKernelRightBlock (supportedRadicalRows
      (supportedRadicalGoodRowEquiv B U hK x hg hdim) (supportedRadicalScalarTest U x d)
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) =
      ContinuousLinearMap.id ℝ U := by
  apply ContinuousLinearMap.ext
  intro u
  apply (supportedRadicalGoodRowEquiv B U hK x hg hdim).injective
  apply ContinuousLinearMap.ext
  intro k
  change supportedRadicalGoodRowEquiv B U hK x hg hdim
      (supportedRadicalRows (supportedRadicalGoodRowEquiv B U hK x hg hdim)
        (supportedRadicalScalarTest U x d)
        ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL) (0, u)) k = _
  rw [supportedRadicalRows_apply, supportedRadicalGoodRowEquiv_apply]
  change inner ℝ (U.orthogonalProjectionOnto x : V)
      (d (supportedRadicalCoordinateOperatorMap U d k (0, u))) =
    inner ℝ ((symmetricSquareToSelfAdjoint k.val).val (U.orthogonalProjectionOnto x)) u
  rw [supportedRadicalCoordinateOperatorMap_apply, hdU]
  exact ((symmetricSquareToSelfAdjoint k.val).property.isSymmetric
    (U.orthogonalProjectionOnto x : V) (u : V)).symm

/-- The actual scalar left block is zero, since the original supported operators annihilate
the chosen normal. Source: `prop:supported-rank`, the common radical at the base. -/
theorem supportedRadicalGoodRow_leftBlock (B : SymmetricSquare V →ₗ[ℝ] W)
    (U : Submodule ℝ V) (hK : B.ker ≤ (symmetricSquareLinearMap U.subtype).range)
    (x : V) (hg : LinearSecondFormGoodCovector B (innerₗ V x))
    (hdim : Module.finrank ℝ B.ker = Module.finrank ℝ U) (d : (ℝ × U) ≃L[ℝ] V)
    (e : V) (he : e ∈ Uᗮ) (hde : d (1, 0) = e) :
    supportedKernelLeftBlock (supportedRadicalRows
      (supportedRadicalGoodRowEquiv B U hK x hg hdim) (supportedRadicalScalarTest U x d)
      ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL)) = 0 := by
  apply ContinuousLinearMap.ext
  intro t
  apply (supportedRadicalGoodRowEquiv B U hK x hg hdim).injective
  apply ContinuousLinearMap.ext
  intro k
  have hr := (symmetricSquare_mem_range_iff_operator_range U k.val).mp (hK k.property)
  have hk := quadraticSpace_kills_orthogonal (symmetricSquareToSelfAdjoint k.val).val
    (symmetricSquareToSelfAdjoint k.val).property.isSymmetric U hr he
  have hdt : d (t, 0) = t • e := by
    rw [← hde, ← map_smul]
    congr 1
    ext <;> simp
  change supportedRadicalGoodRowEquiv B U hK x hg hdim
      (supportedRadicalRows (supportedRadicalGoodRowEquiv B U hK x hg hdim)
        (supportedRadicalScalarTest U x d)
        ((supportedRadicalCoordinateOperatorMap U d).comp B.ker.subtypeL) (t, 0)) k = _
  rw [supportedRadicalRows_apply]
  simp only [zero_apply, map_zero]
  change inner ℝ (U.orthogonalProjectionOnto x : V)
      (d (supportedRadicalCoordinateOperatorMap U d k (t, 0))) = 0
  rw [supportedRadicalCoordinateOperatorMap_apply, hdt, map_smul, hk, smul_zero,
    inner_zero_right]

end GlobalEmbedding.Paper
