import Smoothing.Round4KernelMarginTransport
import GlobalEmbedding.Offline.GoodDictionaryMargins

/-! Quantitative transport on the SAME covector kernel and the original
Hilbert tensor quotient norm. The loss is the squared norm of the genuine
coordinate-to-tangent differential; no auxiliary norm or normalization is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped TensorProduct
namespace GlobalEmbedding.Continuation
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
private local instance kernelMarginRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _
private local instance kernelMarginSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {D E V : Type*}
  [NormedAddCommGroup D] [InnerProductSpace ℝ D] [FiniteDimensional ℝ D]
  [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Pure covariance of the actual canonical kernel restriction. No
Riemannian norm bound is required for this qualitative GoodCovector claim. -/
theorem round4_good_covector_coordinate_to_intrinsic
    (A : D ≃L[ℝ] E) (xi : D →L[ℝ] ℝ)
    (B : SymmetricSquare D →L[ℝ] V) (T : SymmetricSquare E →L[ℝ] V)
    (hBT : B = T.comp (symmetricSquareMapL A.toContinuousLinearMap))
    (hGood : LinearSecondFormGoodCovector B.toLinearMap xi.toLinearMap) :
    LinearSecondFormGoodCovector T.toLinearMap (xi.comp A.symm.toContinuousLinearMap).toLinearMap := by
  obtain ⟨hxi,hinj⟩ := (linearSecondFormGoodCovector_iff_native_restriction B xi).mp hGood
  apply (linearSecondFormGoodCovector_iff_native_restriction T _).mpr
  refine ⟨?_,?_⟩
  · intro hz
    apply hxi
    ext v
    have h := congrArg (fun L : E →L[ℝ] ℝ => L (A v)) hz
    change xi (A.symm (A v)) = 0 at h
    change xi v = 0
    simpa only [A.symm_apply_apply] using h
  · let e := round4CovectorKernelEquiv A xi
    intro u v huv
    have htransport (w : SymmetricSquare (xi.comp A.symm.toContinuousLinearMap).ker) :
        covectorRestriction B xi (symmetricSquareMap e.symm.toContinuousLinearMap w) =
          covectorRestriction T (xi.comp A.symm.toContinuousLinearMap) w := by
      have h := round4_covector_restriction_transport A xi B T hBT
        (symmetricSquareMap e.symm.toContinuousLinearMap w)
      have hi : symmetricSquareMap e.toContinuousLinearMap
          (symmetricSquareMap e.symm.toContinuousLinearMap w) = w := by
        simpa only [ContinuousLinearEquiv.symm_symm] using symmetricSquareMap_symm e.symm w
      exact h.trans (congrArg (covectorRestriction T (xi.comp A.symm.toContinuousLinearMap)) hi)
    have hpre := hinj ((htransport u).trans (huv.trans (htransport v).symm))
    have hpost := congrArg (symmetricSquareMap e.toContinuousLinearMap) hpre
    calc
      u = symmetricSquareMap e.toContinuousLinearMap
          (symmetricSquareMap e.symm.toContinuousLinearMap u) := (symmetricSquareMap_symm e.symm u).symm
      _ = symmetricSquareMap e.toContinuousLinearMap
          (symmetricSquareMap e.symm.toContinuousLinearMap v) := hpost
      _ = v := symmetricSquareMap_symm e.symm v

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_good_covector_coordinate_to_intrinsic
