import Initialization.Phase.CoefficientKernel
import GlobalEmbedding.Paper.CovectorRestriction
import GlobalEmbedding.Paper.SymmetricSquareLinearMapEquality

/-!
# Algebraic good-kernel transport without an auxiliary tangent metric

The original `GoodCovector` predicate is norm independent. These small naturality
lemmas transport it along the genuine chart differential using the already
existing exact binary symmetric-square quotient. They require no inner product
or margin on the original tangent space.
-/

noncomputable section
open GlobalEmbedding.Paper
open scoped TensorProduct

namespace GlobalEmbedding.Initialization

/-- Product evaluation of the existing algebraic symmetric-square functor. -/
@[simp] theorem initialization_symmetricSquareLinearMap_product
    {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    (a : U →ₗ[ℝ] V) (v w : U) :
    symmetricSquareLinearMap a (symmetricSquareProduct U v w) =
      symmetricSquareProduct V (a v) (a w) := by
  exact symmetricBilinearDescend_product (((symmetricSquareProduct V).compl₂ a).comp a)
    (fun v w ↦ symmetricSquareProduct_comm V (a v) (a w)) v w

/-- An actual equivalence induces an injective map on the same algebraic
symmetric square, without choosing a norm on either quotient. -/
theorem initialization_symmetricSquareLinearEquiv_injective
    {U V : Type*} [AddCommGroup U] [Module ℝ U] [AddCommGroup V] [Module ℝ V]
    (a : U ≃ₗ[ℝ] V) : Function.Injective (symmetricSquareLinearMap a.toLinearMap) := by
  have hleft : (symmetricSquareLinearMap a.symm.toLinearMap).comp
      (symmetricSquareLinearMap a.toLinearMap) = LinearMap.id := by
    apply (symmetricSquareRelations U).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change symmetricSquareLinearMap a.symm.toLinearMap
      (symmetricSquareLinearMap a.toLinearMap (symmetricSquareProduct U v w)) = _
    simp only [initialization_symmetricSquareLinearMap_product, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply]
    rfl
  intro v w hvw
  have h := congrArg (symmetricSquareLinearMap a.symm.toLinearMap) hvw
  change ((symmetricSquareLinearMap a.symm.toLinearMap).comp
    (symmetricSquareLinearMap a.toLinearMap)) v =
    ((symmetricSquareLinearMap a.symm.toLinearMap).comp
      (symmetricSquareLinearMap a.toLinearMap)) w at h
  simpa only [hleft, LinearMap.id_apply] using h

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

/-- Pulling an actual good chart hyperplane back by an actual chart equivalence
preserves injectivity of its true entire second-form restriction. The source
only needs its existing normed-space topology, with no auxiliary inner product. -/
theorem initialization_kernel_pullback_injective
    {U E V : Type*} [NormedAddCommGroup U] [NormedSpace ℝ U]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup V] [NormedSpace ℝ V]
    (a : U ≃L[ℝ] E) (ξ : E →L[ℝ] ℝ) (R : SymmetricSquare E →L[ℝ] V)
    (hinj : Function.Injective (covectorRestriction R ξ)) :
    Function.Injective
      (((R.toLinearMap.comp (symmetricSquareLinearMap a.toLinearMap))).comp
        (symmetricSquareLinearMap (ξ.comp a.toContinuousLinearMap).ker.subtype)) := by
  let e := coefficientKernelEquiv a ξ
  have heq : ((R.toLinearMap.comp (symmetricSquareLinearMap a.toLinearMap))).comp
      (symmetricSquareLinearMap (ξ.comp a.toContinuousLinearMap).ker.subtype) =
      (covectorRestriction R ξ).toLinearMap.comp (symmetricSquareLinearMap e.toLinearMap) := by
    apply (symmetricSquareRelations (ξ.comp a.toContinuousLinearMap).ker).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change R (symmetricSquareLinearMap a.toLinearMap
      (symmetricSquareLinearMap (ξ.comp a.toContinuousLinearMap).ker.subtype
        (symmetricSquareProduct (ξ.comp a.toContinuousLinearMap).ker v w))) =
      covectorRestriction R ξ (symmetricSquareLinearMap e.toLinearMap
        (symmetricSquareProduct (ξ.comp a.toContinuousLinearMap).ker v w))
    simp only [initialization_symmetricSquareLinearMap_product,
      covectorRestriction, ContinuousLinearMap.comp_apply, symmetricSquareMapL_product]
    rfl
  rw [heq]
  exact hinj.comp (initialization_symmetricSquareLinearEquiv_injective e.toLinearEquiv)

end GlobalEmbedding.Initialization
