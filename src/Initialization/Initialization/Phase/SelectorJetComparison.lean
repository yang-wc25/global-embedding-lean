import Initialization.Phase.SelectorCoframe
import Initialization.Assembly.SelectorSecondChain

/-!
# The literal second derivative and its canonical quotient error

The first-jet comparison uses the actual coefficient field. Differentiating
that field produces the actual bilinear coefficient derivative. Its symmetric
part descends by the original `actualHessianLift`, and its image under the
selector first jet is exactly the tangent term already proved harmless.
The remaining operator is a genuine difference of the actual second derivative
and the actual orbit-Hessian model; no candidate second jet is supplied.
-/

noncomputable section
open Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance comparisonRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance comparisonSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

section Lift

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- The existing canonical symmetrization commutes with the same actual
coefficient map in both arguments, on the entire symmetric-square quotient. -/
theorem actualHessianLift_bilinearComp (B : F →L[ℝ] F →L[ℝ] V) (c : E →L[ℝ] F) :
    actualHessianLift (B.bilinearComp c c) =
      (actualHessianLift B).comp (symmetricSquareMapL c) := by
  apply ContinuousLinearMap.coe_injective
  apply (symmetricSquareRelations E).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change symmetrizedHessianJet (B.bilinearComp c c) (symmetricSquareProduct E v w) =
    actualHessianLift B (symmetricSquareMapL c (symmetricSquareProduct E v w))
  rw [symmetricSquareMapL_product]
  change symmetrizedHessianJet (B.bilinearComp c c) (symmetricSquareProduct E v w) =
    symmetrizedHessianJet B (symmetricSquareProduct F (c v) (c w))
  rw [symmetrizedHessianJet_product, symmetrizedHessianJet_product]
  rfl

/-- Postcomposition commutes with the original lift, even for a coefficient
derivative which is not symmetric. Its symmetric part is handled explicitly. -/
theorem actualHessianLift_postcomp (B : E →L[ℝ] E →L[ℝ] F) (post : F →L[ℝ] V) :
    actualHessianLift (((ContinuousLinearMap.compL ℝ E F V) post).comp B) =
      post.comp (actualHessianLift B) := by
  apply ContinuousLinearMap.coe_injective
  apply (symmetricSquareRelations E).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change symmetrizedHessianJet (((ContinuousLinearMap.compL ℝ E F V) post).comp B)
      (symmetricSquareProduct E v w) =
    post (symmetrizedHessianJet B (symmetricSquareProduct E v w))
  rw [symmetrizedHessianJet_product, symmetrizedHessianJet_product]
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.compL_apply,
    map_smul, map_add]

end Lift

section Selector

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {n N : ℕ} (C : Fin n → ℕ) [∀ i, Fact (0 < C i)]
  (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))

/-- The actual orbit Hessian on arbitrary vectors has the exact double Hopf
sum, in the same order as the differentiated selected-map formula. -/
theorem selectorIdealSecondJet_product
    (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
    (z : FreeHopfProduct C) (v w : EuclideanSpace ℝ (Fin n)) :
    selectorIdealSecondJet C S z (symmetricSquareProduct (EuclideanSpace ℝ (Fin n)) v w) =
      ∑ i, w i • ∑ j, v j • freeHopfDeriv C j (freeHopfDeriv C i S) z := by
  let b := (EuclideanSpace.basisFun (Fin n) ℝ).toBasis
  conv_lhs => rw [← b.sum_repr v, ← b.sum_repr w]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
  simp only [b, OrthonormalBasis.coe_toBasis, OrthonormalBasis.coe_toBasis_repr_apply,
    EuclideanSpace.basisFun_repr, EuclideanSpace.basisFun_apply,
    selectorIdealSecondJet_basis_product C S hS]

/-- Literal coefficient covectors, obtained by coordinate projections from the
same actual coframe operator field. -/
def selectorCoframeRates (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n))
    (x : E) (i : Fin n) : E →L[ℝ] ℝ :=
  (EuclideanSpace.proj i).comp (c x)

@[simp] theorem selectorCoframeRates_apply
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x v : E) (i : Fin n) :
    selectorCoframeRates c x i v = c x v i := rfl

/-- The raw main term uses the SAME actual selector orbit Hessian at z(x). -/
def selectorSourceMainBilinear (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : E) :
    E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (fderiv ℝ (fderiv ℝ (S ∘ freeHopfOrbitLift C (z x))) 0).bilinearComp (c x) (c x)

/-- The tangent bilinear term uses the actual derivative of that coframe. -/
def selectorSourceTangentBilinear (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : E) :
    E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  ((ContinuousLinearMap.compL ℝ E (EuclideanSpace ℝ (Fin n))
    (EuclideanSpace ℝ (Fin N))) (selectorIdealFirstJet C S (z x))).comp (fderiv ℝ c x)

/-- The literal second-derivative remainder of the same selected map. -/
def selectorSourceSecondError (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : E) :
    E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  fderiv ℝ (fderiv ℝ (S ∘ z)) x - selectorSourceMainBilinear C S z c x -
    selectorSourceTangentBilinear C S z c x

/-- Exact whole-operator identification in the original canonical quotient.
The coframe correction is the lift of its ACTUAL derivative, not supplied data. -/
theorem coordinateHessianJet_selector_error (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : E) :
    coordinateHessianJet (S ∘ z) x -
      ((selectorIdealSecondJet C S (z x)).comp (symmetricSquareMapL (c x)) +
        (selectorIdealFirstJet C S (z x)).comp (actualHessianLift (fderiv ℝ c x))) =
      actualHessianLift (selectorSourceSecondError C S z c x) := by
  simp only [selectorSourceSecondError, map_sub, selectorSourceMainBilinear,
    selectorSourceTangentBilinear, actualHessianLift_bilinearComp, actualHessianLift_postcomp,
    coordinateHessianJet, selectorIdealSecondJet]
  abel

/-- The resulting canonical quotient error costs only the already established
fixed Hessian-lift constant for these fixed source and target normed spaces. -/
theorem coordinateHessianJet_selector_error_norm_le (z : E → FreeHopfProduct C)
    (c : E → E →L[ℝ] EuclideanSpace ℝ (Fin n)) (x : E) :
    ‖coordinateHessianJet (S ∘ z) x -
      ((selectorIdealSecondJet C S (z x)).comp (symmetricSquareMapL (c x)) +
        (selectorIdealFirstJet C S (z x)).comp (actualHessianLift (fderiv ℝ c x)))‖ ≤
      actualHessianLiftConstant E (EuclideanSpace ℝ (Fin N)) *
        ‖selectorSourceSecondError C S z c x‖ := by
  rw [coordinateHessianJet_selector_error]
  have h := actualHessianLift_sub_norm_le (selectorSourceSecondError C S z c x)
    (0 : E →L[ℝ] E →L[ℝ] EuclideanSpace ℝ (Fin N))
  simpa only [map_zero, sub_zero, actualHessianLiftConstant] using h

end Selector

end GlobalEmbedding.Initialization
