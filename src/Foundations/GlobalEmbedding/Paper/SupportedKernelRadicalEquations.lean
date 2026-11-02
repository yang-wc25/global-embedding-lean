import GlobalEmbedding.Paper.SupportedKernelParametrization
import GlobalEmbedding.Paper.SupportedRadicalGoodRowBlock
import GlobalEmbedding.Paper.SupportedRadicalNormalResidual
import GlobalEmbedding.Paper.SupportedRadicalClosedIncidence
import GlobalEmbedding.Paper.SymmetricSquareUnitRadical
import Mathlib.Analysis.InnerProductSpace.ProdL2

/-!
# The original operator's actual local radical equations

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:supported-rank`,
lines 1004–1012 and 1018–1022. Compose the sole actual kernel family with the original
binary-quotient operator action and the SAME normal residual. Its zeros are precisely
the literal supported-kernel predicate on the genuine invertible-block domain.
-/

noncomputable section
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Paper

variable {V W : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup W] [InnerProductSpace ℝ W]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
attribute [local instance] operatorSquareRelationsClosed operatorSquareNormed
attribute [local instance] operatorSelfAdjointContinuousSMul

local instance localRadicalSquareInner : InnerProductSpace ℝ (SymmetricSquare V) :=
  { Submodule.instQuotientInnerProductSpace (symmetricSquareRelations V) with
    toNormedSpace := squareNS V }

-- Pin the native operator parents before forming the nested operator space.
local instance localRadicalCoordinateOperatorNormed (U : Submodule ℝ V) :
    NormedAddCommGroup ((ℝ × U) →L[ℝ] (ℝ × U)) := inferInstance

local instance localRadicalCoordinateOperatorSpace (U : Submodule ℝ V) :
    NormedSpace ℝ ((ℝ × U) →L[ℝ] (ℝ × U)) := inferInstance

/-- The actual original operators on the actual nearby kernel, in fixed genuine V coordinates.
Source: `prop:supported-rank`, local kernel graph and common-radical equations. -/
def supportedKernelRadicalFamily (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (C : SymmetricSquare V →L[ℝ] W) : B.ker →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U)) :=
  (supportedRadicalCoordinateOperatorMap U d).comp (supportedKernelParametrization B hB C)

/-- The SAME actual normal residual, now evaluated on the original B-operator space.
Source: `prop:supported-rank`, genuine local defining equations. -/
def supportedKernelRadicalEquation (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (C : SymmetricSquare V →L[ℝ] W) :
    B.ker →L[ℝ] r.ker :=
  supportedRadicalNormalResidual a r w hw (supportedKernelRadicalFamily B hB U d C)

/-- The actual family is smooth at EVERY genuine invertible kernel block.
Source: `prop:supported-rank`, one common open smooth chart domain. -/
theorem supportedKernelRadicalFamily_contDiffAt (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (C : SymmetricSquare V →L[ℝ] W) (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) :
    ContDiffAt ℝ ∞ (supportedKernelRadicalFamily B hB U d) C := by
  let L : (B.ker →L[ℝ] SymmetricSquare V) →L[ℝ]
      (B.ker →L[ℝ] ((ℝ × U) →L[ℝ] (ℝ × U))) :=
    ContinuousLinearMap.compL ℝ B.ker (SymmetricSquare V)
      ((ℝ × U) →L[ℝ] (ℝ × U)) (supportedRadicalCoordinateOperatorMap U d)
  have hL : ContDiff ℝ ∞ L := by fun_prop
  simpa only [supportedKernelRadicalFamily, L] using!
    hL.contDiffAt.comp C (supportedKernelParametrization_contDiffAt B hB C e hA)

/-- The SAME original equation is smooth at EVERY point where both actual blocks invert.
Source: `prop:supported-rank`, genuine smooth local defining equations. -/
theorem supportedKernelRadicalEquation_contDiffAt (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (C : SymmetricSquare V →L[ℝ] W)
    (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) (f : U ≃L[ℝ] U)
    (hR : supportedKernelRightBlock
      (supportedRadicalRows a r (supportedKernelRadicalFamily B hB U d C)) =
        (f : U →L[ℝ] U)) :
    ContDiffAt ℝ ∞ (supportedKernelRadicalEquation B hB U d a r w hw) C := by
  have hF := supportedKernelRadicalFamily_contDiffAt B hB U d C e hA
  have hN := supportedRadicalNormalResidual_contDiffAt a r w hw _ f hR
  simpa only [supportedKernelRadicalEquation] using! hN.comp C hF

/-- The original equation has EXACTLY the original literal supported-kernel zero set.
Proof: actual kernel parameterization identifies all radical equations with those on ker C;
the genuine coordinate equivalence preserves nonzero radicals. The sole accepted unit-radical
dictionary converts this to the original codimension-one support predicate. No desired
geometry is assumed. Source: `prop:supported-rank`, local locus identification. -/
theorem supportedKernelRadicalEquation_eq_zero_iff (B : SymmetricSquare V →L[ℝ] W)
    (hB : Function.Surjective B) (U : Submodule ℝ V) (d : (ℝ × U) ≃L[ℝ] V)
    (a : U ≃L[ℝ] (B.ker →L[ℝ] ℝ)) (r : (ℝ × U) →L[ℝ] ℝ)
    (w : ℝ × U) (hw : r w = 1) (C : SymmetricSquare V →L[ℝ] W)
    (e : B.kerᗮ ≃L[ℝ] B.kerᗮ)
    (hA : supportedKernelRightBlock (supportedRankKernelChartOperator B hB C) =
      (e : B.kerᗮ →L[ℝ] B.kerᗮ)) (f : U ≃L[ℝ] U)
    (hR : supportedKernelRightBlock
      (supportedRadicalRows a r (supportedKernelRadicalFamily B hB U d C)) =
        (f : U →L[ℝ] U)) :
    supportedKernelRadicalEquation B hB U d a r w hw C = 0 ↔
      HasSupportedKernel C.toLinearMap := by
  rw [supportedKernelRadicalEquation,
    supportedRadicalNormalResidual_eq_zero_iff a r w hw _ f hR,
    supportedRadicalResidual_eq_zero_iff a r _ f hR,
    hasSupportedKernel_iff_unit_common_radical]
  constructor
  · rintro ⟨v, hv, hvQ⟩
    let M : SymmetricSquare V →L[ℝ] (V →L[ℝ] V) :=
      (selfAdjoint.submodule ℝ (V →L[ℝ] V)).subtypeL.comp
        symmetricSquareSelfAdjointCLE.toContinuousLinearMap
    let N : C.ker →L[ℝ] (V →L[ℝ] V) := M.comp C.ker.subtypeL
    have hnonzero : ∃ v' : V, v' ≠ 0 ∧ ∀ k : C.ker, N k v' = 0 := by
      refine ⟨d v, ?_, ?_⟩
      · intro h
        apply hv
        exact d.injective (h.trans d.map_zero.symm)
      · intro k
        have hk : k.val ∈ (supportedKernelParametrization B hB C).range := by
          rw [supportedKernelParametrization_range B hB C e hA]
          exact k.property
        obtain ⟨k', hk'⟩ := hk
        change (symmetricSquareToSelfAdjoint k.val).val (d v) = 0
        rw [← hk', ← supportedRadicalCoordinateOperatorMap_apply U d]
        have h := congrArg d (hvQ k')
        simpa only [supportedKernelRadicalFamily, ContinuousLinearMap.comp_apply,
          map_zero] using! h
    obtain ⟨v', hv', hNv⟩ := (hasUnitCommonRadical_iff N).mpr hnonzero
    exact ⟨v', hv', fun q hq ↦ hNv ⟨q, hq⟩⟩
  · rintro ⟨v, hv, hvQ⟩
    refine ⟨d.symm v, ?_, ?_⟩
    · intro h
      have hz : v = 0 := by simpa only [map_zero, d.apply_symm_apply] using congrArg d h
      simp [hz] at hv
    · intro k
      apply d.injective
      change d (supportedRadicalCoordinateOperatorMap U d
        (supportedKernelParametrization B hB C k) (d.symm v)) = d 0
      rw [supportedRadicalCoordinateOperatorMap_apply, d.apply_symm_apply, map_zero]
      apply hvQ
      rw [← supportedKernelParametrization_range B hB C e hA]
      exact ⟨k, rfl⟩

end GlobalEmbedding.Paper
