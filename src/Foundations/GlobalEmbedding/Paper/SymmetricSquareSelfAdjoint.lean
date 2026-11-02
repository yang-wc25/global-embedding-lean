import GlobalEmbedding.Paper.SymmetricBilinearDescendEvaluation
import GlobalEmbedding.Paper.QuotientContraction
import GlobalEmbedding.Paper.SymmetricSquareNorms
import Mathlib.Analysis.CStarAlgebra.Basic
import Mathlib.Analysis.InnerProductSpace.Adjoint
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# The original binary symmetric square as real self-adjoint operators

Source: original `prop:saturation`, lines 948–995, and normalized product at
1129–1130. DAG: `symmetric-square-selfadjoint-operator`. Exclusive worker W2.
The quotient and its product are the existing project objects. The native
self-adjoint part of a rank-one operator supplies exactly the required half-sum.
-/

noncomputable section
open scoped TensorProduct
open InnerProductSpace

namespace GlobalEmbedding.Paper

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The existing real rank-one map, symmetrized by Mathlib's self-adjoint part.
Source: the normalized product in `prop:saturation`. -/
def symmetricSquareOperatorBeta : V →ₗ[ℝ] V →ₗ[ℝ] selfAdjoint (V →L[ℝ] V) where
  toFun v := (selfAdjointPart ℝ).comp (rankOne ℝ v).toLinearMap
  map_add' v w := by
    ext x
    simp
  map_smul' c v := by
    ext x
    simp

/-- The symmetrized rank-one map is symmetric in its vector arguments.
Source: normalized product `v ⊙ w`. -/
theorem symmetricSquareOperatorBeta_comm (v w : V) :
    symmetricSquareOperatorBeta v w = symmetricSquareOperatorBeta w v := by
  apply Subtype.ext
  simp [symmetricSquareOperatorBeta, selfAdjointPart_apply_coe,
    ContinuousLinearMap.star_eq_adjoint, add_comm]

/-- The actual binary quotient-to-operator map, using the accepted descent.
Source: contraction notation in `prop:saturation`. -/
def symmetricSquareToSelfAdjoint :
    SymmetricSquare V →ₗ[ℝ] selfAdjoint (V →L[ℝ] V) :=
  symmetricBilinearDescend symmetricSquareOperatorBeta symmetricSquareOperatorBeta_comm

/-- Product evaluation preserves the factor one half in the original source.
Source: original normalized product and the contraction `Pξ`. -/
theorem symmetricSquareToSelfAdjoint_product (v w x : V) :
    (symmetricSquareToSelfAdjoint (symmetricSquareProduct V v w)).val x =
      (1 / 2 : ℝ) • (inner ℝ w x • v + inner ℝ v x • w) := by
  rw [symmetricSquareToSelfAdjoint, symmetricBilinearDescend_product]
  simp [symmetricSquareOperatorBeta, selfAdjointPart_apply_coe,
    ContinuousLinearMap.star_eq_adjoint]

/-- Orthonormal reconstruction in the original quotient, with no coordinate carrier.
Source: the inverse of the normalized quadratic-form realization. -/
def symmetricSquareFromSelfAdjoint {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) :
    selfAdjoint (V →L[ℝ] V) →ₗ[ℝ] SymmetricSquare V where
  toFun A := ∑ i, symmetricSquareProduct V (b i) (A.val (b i))
  map_add' A B := by
    simp only [AddSubgroup.coe_add, add_apply, map_add,
      Finset.sum_add_distrib]
  map_smul' c A := by
    simp [Finset.smul_sum]

private theorem symmetricSquareFromSelfAdjoint_product {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) (v w : V) :
    symmetricSquareFromSelfAdjoint b
      (symmetricSquareToSelfAdjoint (symmetricSquareProduct V v w)) =
        symmetricSquareProduct V v w := by
  have hs (u : V) : ∑ i, inner ℝ u (b i) • b i = u := by
    simpa only [real_inner_comm] using b.sum_repr' u
  have hp (u z : V) :
      ∑ i, inner ℝ u (b i) • symmetricSquareProduct V (b i) z =
        symmetricSquareProduct V u z := by
    simpa only [map_sum, map_smul, LinearMap.flip_apply] using
      congrArg ((symmetricSquareProduct V).flip z) (hs u)
  change (∑ i, symmetricSquareProduct V (b i)
    ((symmetricSquareToSelfAdjoint (symmetricSquareProduct V v w)).val (b i))) = _
  simp only [symmetricSquareToSelfAdjoint_product, map_smul, map_add]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, hp, hp,
    symmetricSquareProduct_comm V w v]
  rw [← two_smul ℝ (symmetricSquareProduct V v w), smul_smul]
  norm_num

/-- The explicit inverse is a left inverse on the entire binary quotient.
Source: quotient/tensor extensionality applied to normalized product reconstruction. -/
theorem symmetricSquareFromSelfAdjoint_leftInverse {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) :
    (symmetricSquareFromSelfAdjoint b).comp symmetricSquareToSelfAdjoint =
      LinearMap.id := by
  apply (symmetricSquareRelations V).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  exact symmetricSquareFromSelfAdjoint_product b v w

/-- Orthonormal reconstruction is a right inverse for actual self-adjoint operators.
Source: real symmetric quadratic-form realization, using the same quotient products. -/
theorem symmetricSquareFromSelfAdjoint_rightInverse {ι : Type*} [Fintype ι]
    (b : OrthonormalBasis ι ℝ V) :
    symmetricSquareToSelfAdjoint.comp (symmetricSquareFromSelfAdjoint b) =
      LinearMap.id := by
  apply LinearMap.ext
  intro A
  apply Subtype.ext
  ext x
  have hfirst : (∑ i, inner ℝ (A.val (b i)) x • b i) = A.val x := by
    calc
      _ = ∑ i, inner ℝ (b i) (A.val x) • b i := by
        apply Finset.sum_congr rfl
        intro i _
        exact congrArg (fun c : ℝ ↦ c • b i) (A.property.isSymmetric (b i) x)
      _ = _ := b.sum_repr' (A.val x)
  have hsecond : (∑ i, inner ℝ (b i) x • A.val (b i)) = A.val x := by
    simpa only [map_sum, map_smul] using congrArg A.val (b.sum_repr' x)
  change ((selfAdjoint (V →L[ℝ] V)).subtype (symmetricSquareToSelfAdjoint
    (∑ i, symmetricSquareProduct V (b i) (A.val (b i))))) x = A.val x
  rw [map_sum, map_sum]
  simp only [sum_apply]
  change (∑ i, (symmetricSquareToSelfAdjoint
    (symmetricSquareProduct V (b i) (A.val (b i)))).val x) = A.val x
  simp_rw [symmetricSquareToSelfAdjoint_product]
  rw [← Finset.smul_sum, Finset.sum_add_distrib, hfirst, hsecond]
  rw [← two_smul ℝ (A.val x), smul_smul]
  norm_num

/-- The faithful real linear equivalence from the original binary quotient.
Source: `prop:saturation`, the self-adjoint realization of its actual tensors. -/
def symmetricSquareSelfAdjointEquiv :
    SymmetricSquare V ≃ₗ[ℝ] selfAdjoint (V →L[ℝ] V) :=
  let b := stdOrthonormalBasis ℝ V
  { symmetricSquareToSelfAdjoint with
    invFun := symmetricSquareFromSelfAdjoint b
    left_inv := fun q ↦ congrArg (fun f : SymmetricSquare V →ₗ[ℝ] SymmetricSquare V ↦ f q)
      (symmetricSquareFromSelfAdjoint_leftInverse b)
    right_inv := fun A ↦ congrArg
      (fun f : selfAdjoint (V →L[ℝ] V) →ₗ[ℝ] selfAdjoint (V →L[ℝ] V) ↦ f A)
      (symmetricSquareFromSelfAdjoint_rightInverse b) }

/-- The operator evaluates by the SAME previously defined quotient contraction.
Source: `Pξ` in the original saturation proof, with the real Riesz covector. -/
theorem symmetricSquareToSelfAdjoint_apply (q : SymmetricSquare V) (x : V) :
    (symmetricSquareToSelfAdjoint q).val x =
      contractionKernelQuotientMap (innerₗ V x) q := by
  let ev : selfAdjoint (V →L[ℝ] V) →ₗ[ℝ] V :=
    { toFun := fun A ↦ A.val x
      map_add' := fun A B ↦ by simp
      map_smul' := fun c A ↦ by simp }
  have h : ev.comp symmetricSquareToSelfAdjoint =
      contractionKernelQuotientMap (innerₗ V x) := by
    apply (symmetricSquareRelations V).linearMap_qext
    apply TensorProduct.ext'
    intro v w
    change (symmetricSquareToSelfAdjoint (symmetricSquareProduct V v w)).val x =
      contractionKernelQuotientMap (innerₗ V x) (symmetricSquareProduct V v w)
    rw [symmetricSquareToSelfAdjoint_product, contractionKernelQuotientMap_product]
    simp only [innerₗ_apply_apply]
    simp [real_inner_comm, add_comm]
  exact congrArg (fun f : SymmetricSquare V →ₗ[ℝ] V ↦ f q) h

/-- Evaluation of the equivalence is the original contraction, not a replacement.
Source: the operator dictionary used by `prop:saturation`. -/
theorem symmetricSquareSelfAdjointEquiv_apply (q : SymmetricSquare V) (x : V) :
    (symmetricSquareSelfAdjointEquiv q).val x =
      contractionKernelQuotientMap (innerₗ V x) q :=
  symmetricSquareToSelfAdjoint_apply q x

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

local instance operatorSquareRelationsClosed :
    IsClosed (symmetricSquareRelations V : Set (V ⊗[ℝ] V)) :=
  Submodule.closed_of_finiteDimensional _

local instance operatorSquareNormed : NormedAddCommGroup (SymmetricSquare V) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations V)

local instance operatorSelfAdjointContinuousSMul :
    ContinuousSMul ℝ (selfAdjoint (V →L[ℝ] V)) :=
  show ContinuousSMul ℝ (selfAdjoint.submodule ℝ (V →L[ℝ] V)) from inferInstance

/-- The same equivalence is continuous in the ORIGINAL Hilbert tensor quotient norm.
No change of norm or operator-norm isometry is asserted. Source: the finite-dimensional
Euclidean dictionary in `prop:saturation` and `prop:supported-rank`. -/
def symmetricSquareSelfAdjointCLE :
    SymmetricSquare V ≃L[ℝ] selfAdjoint (V →L[ℝ] V) :=
  symmetricSquareSelfAdjointEquiv.toContinuousLinearEquiv

/-- The CLE retains exactly the original contraction evaluation.
Source: the same quotient and the same normalized product. -/
theorem symmetricSquareSelfAdjointCLE_apply (q : SymmetricSquare V) (x : V) :
    (symmetricSquareSelfAdjointCLE q).val x =
      contractionKernelQuotientMap (innerₗ V x) q :=
  symmetricSquareSelfAdjointEquiv_apply q x

end GlobalEmbedding.Paper
