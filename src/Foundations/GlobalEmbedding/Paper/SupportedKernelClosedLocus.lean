import GlobalEmbedding.Paper.SupportedLocusLocalEquations
import GlobalEmbedding.Paper.SupportedKernelRadicalClosed
import GlobalEmbedding.Paper.SymmetricSquareUnitRadical
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!+# Relative closedness of the original literal supported-kernel locus

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 998–1006. Use the sole original quotient/operator support dictionary to identify a
supported kernel with an actual unit common radical. Pull the proved actual onto-kernel
radical closedness back to the exact original onto/phase-regular ambient. The symmetric
square, its norm and the original support predicate are unchanged.
-/

noncomputable section

open scoped TensorProduct

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]
  [FiniteDimensional ℝ W]


open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] operatorSelfAdjointContinuousSMul

/-- The FULL original literal supported-kernel locus is relatively closed among actual onto
operators. The Hilbert structure is the native one on the SAME tensor quotient norm, and
the support/common-radical equivalence is proved internally.
Source: `prop:supported-rank`, relative closedness. -/
theorem isClosed_supportedKernel_surjective :
    IsClosed {B : {B : SymmetricSquare V →L[ℝ] W | Function.Surjective B} |
      HasSupportedKernel (B : SymmetricSquare V →L[ℝ] W).toLinearMap} := by
  let : InnerProductSpace ℝ (SymmetricSquare V) :=
    { Submodule.instQuotientInnerProductSpace (symmetricSquareRelations V) with
      toNormedSpace := squareNS V }
  let M : SymmetricSquare V →L[ℝ] (V →L[ℝ] V) :=
    (selfAdjoint.submodule ℝ (V →L[ℝ] V)).subtypeL.comp
      symmetricSquareSelfAdjointCLE.toContinuousLinearMap
  have hclosed := supportedKernel_unit_radical_isClosed (W := W) M
  convert hclosed using 1
  ext B
  simp only [Set.mem_ofPred_eq]
  rw [hasSupportedKernel_iff_unit_common_radical]
  rfl

/-- The FULL original literal supported-kernel locus is relatively closed in the EXACT
onto and phase-regular ambient of the original target. This is the first conjunct of that
target, with no assumed manifold or closedness hypothesis.
Source: `prop:supported-rank`, original full-rank phase-regular setting. -/
theorem isClosed_supportedKernel_surjective_phaseRegular :
    IsClosed {B : {B : SymmetricSquare V →L[ℝ] W |
        Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap} |
      HasSupportedKernel (B : SymmetricSquare V →L[ℝ] W).toLinearMap} := by
  let j : {B : SymmetricSquare V →L[ℝ] W |
      Function.Surjective B ∧ LinearSecondFormPhaseRegular B.toLinearMap} →
      {B : SymmetricSquare V →L[ℝ] W | Function.Surjective B} :=
    fun B ↦ ⟨B.1, B.2.1⟩
  have hj : Continuous j := continuous_subtype_val.subtype_mk _
  exact isClosed_supportedKernel_surjective.preimage hj

end GlobalEmbedding.Paper
