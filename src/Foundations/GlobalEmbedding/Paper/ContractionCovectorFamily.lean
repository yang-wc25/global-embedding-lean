import GlobalEmbedding.Paper.QuotientContraction
import GlobalEmbedding.Paper.SymmetricSquareLinearMap
import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Tactic.Module

/-!
# Actual contraction as a linear covector family, without an inner product

Source: original `prop:saturation`, lines 948–953 and 971–995.
DAG: `contraction-covector-parameter-family`, `contraction-covector-naturality`.
Exclusive worker W2. The value is the SAME existing quotient contraction.
Finite-dimensional continuity supplies actual CLMs, without changing quotient norms.
-/

noncomputable section
open scoped TensorProduct
namespace GlobalEmbedding.Paper

section Algebraic
variable {V W : Type*} [AddCommGroup V] [Module ℝ V]
  [AddCommGroup W] [Module ℝ W]

/-- The SAME contraction is linear in its actual algebraic covector parameter.
Source: good-covector openness and conicality in `prop:saturation`. -/
def contractionKernelCovectorLinear :
    (V →ₗ[ℝ] ℝ) →ₗ[ℝ] SymmetricSquare V →ₗ[ℝ] V where
  toFun := contractionKernelQuotientMap
  map_add' ξ η := by
    apply (symmetricSquareRelations V).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change contractionKernelQuotientMap (ξ + η) (symmetricSquareProduct V v w) =
      contractionKernelQuotientMap ξ (symmetricSquareProduct V v w) +
        contractionKernelQuotientMap η (symmetricSquareProduct V v w)
    simp only [contractionKernelQuotientMap_product, LinearMap.add_apply, add_smul]
    module
  map_smul' c ξ := by
    apply (symmetricSquareRelations V).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change contractionKernelQuotientMap (c • ξ) (symmetricSquareProduct V v w) =
      c • contractionKernelQuotientMap ξ (symmetricSquareProduct V v w)
    simp only [contractionKernelQuotientMap_product, LinearMap.smul_apply]
    module

/-- Evaluation retains the original contraction definition exactly.
Source: same covector/tensor pairing, no replacement contraction. -/
theorem contractionKernelCovectorLinear_apply (ξ : V →ₗ[ℝ] ℝ) (q : SymmetricSquare V) :
    contractionKernelCovectorLinear ξ q = contractionKernelQuotientMap ξ q := rfl

/-- The original contraction commutes with the original symmetric-square functor.
Source: the no-inner-product coordinate transfer in `prop:saturation`. -/
theorem contractionKernelQuotientMap_naturality (f : V →ₗ[ℝ] W) (ξ : W →ₗ[ℝ] ℝ) :
    f.comp (contractionKernelQuotientMap (ξ.comp f)) =
      (contractionKernelQuotientMap ξ).comp (symmetricSquareLinearMap f) := by
  apply (symmetricSquareRelations V).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change f (contractionKernelQuotientMap (ξ.comp f) (symmetricSquareProduct V v w)) =
    contractionKernelQuotientMap ξ (symmetricSquareLinearMap f (symmetricSquareProduct V v w))
  have hp := symmetricBilinearDescend_product
    (((symmetricSquareProduct W).compl₂ f).comp f)
    (fun v w ↦ symmetricSquareProduct_comm W (f v) (f w)) v w
  change symmetricSquareLinearMap f (symmetricSquareProduct V v w) =
    symmetricSquareProduct W (f v) (f w) at hp
  rw [hp, contractionKernelQuotientMap_product, contractionKernelQuotientMap_product]
  simp only [map_smul, map_add, LinearMap.comp_apply]

/-- Pointwise naturality for the SAME q, map and covector.
Source: original contraction condition under a linear coordinate change. -/
theorem contractionKernelQuotientMap_naturality_apply (f : V →ₗ[ℝ] W)
    (ξ : W →ₗ[ℝ] ℝ) (q : SymmetricSquare V) :
    f (contractionKernelQuotientMap (ξ.comp f) q) =
      contractionKernelQuotientMap ξ (symmetricSquareLinearMap f q) :=
  congrArg (fun L : SymmetricSquare V →ₗ[ℝ] W ↦ L q)
    (contractionKernelQuotientMap_naturality f ξ)

end Algebraic

section Normed
variable {V K : Type*} [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V] [NormedAddCommGroup K] [NormedSpace ℝ K]
  [FiniteDimensional ℝ K]

/-- For fixed actual q, contraction is a genuine continuous linear covector family.
Source: `prop:saturation`; no inner product is needed on the original source. -/
def contractionKernelCovectorEval (q : SymmetricSquare V) : (V →L[ℝ] ℝ) →L[ℝ] V :=
  ((contractionKernelCovectorLinear.flip q).comp (ContinuousLinearMap.coeLM ℝ)).toContinuousLinearMap

/-- Evaluation of that CLM is the SAME actual contraction.
Source: the original FULL continuous-covector parameter space. -/
theorem contractionKernelCovectorEval_apply (q : SymmetricSquare V) (ξ : V →L[ℝ] ℝ) :
    contractionKernelCovectorEval q ξ = contractionKernelQuotientMap ξ.toLinearMap q := rfl

/-- The actual restricted contractions form a CLM-valued CLM. In particular j may
be the SAME ker(B) inclusion with any compatible internal finite-dimensional norm.
Source: native injective-operator openness applied to the original Good condition. -/
def contractionKernelCovectorOperator (j : K →ₗ[ℝ] SymmetricSquare V) :
    (V →L[ℝ] ℝ) →L[ℝ] (K →L[ℝ] V) := by
  let A : (V →L[ℝ] ℝ) →ₗ[ℝ] (K →L[ℝ] V) :=
    { toFun := fun ξ ↦ ((contractionKernelQuotientMap ξ.toLinearMap).comp j).toContinuousLinearMap
      map_add' := by
        intro ξ η
        ext k
        change contractionKernelCovectorLinear (ξ.toLinearMap + η.toLinearMap) (j k) =
          contractionKernelCovectorLinear ξ.toLinearMap (j k) +
            contractionKernelCovectorLinear η.toLinearMap (j k)
        simp only [map_add, LinearMap.add_apply]
      map_smul' := by
        intro c ξ
        ext k
        change contractionKernelCovectorLinear (c • ξ.toLinearMap) (j k) =
          c • contractionKernelCovectorLinear ξ.toLinearMap (j k)
        simp only [map_smul, LinearMap.smul_apply] }
  exact A.toContinuousLinearMap

/-- Literal value of the actual CLM-valued covector family.
Source: the SAME original cξ restricted through the actual j. -/
theorem contractionKernelCovectorOperator_apply (j : K →ₗ[ℝ] SymmetricSquare V)
    (ξ : V →L[ℝ] ℝ) (k : K) :
    contractionKernelCovectorOperator j ξ k =
      contractionKernelQuotientMap ξ.toLinearMap (j k) := rfl

end Normed
end GlobalEmbedding.Paper
