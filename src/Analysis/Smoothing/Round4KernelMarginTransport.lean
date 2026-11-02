import GlobalEmbedding.Paper.CovectorRestriction
import GlobalEmbedding.Paper.SymmetricSquareTransportLowerBound
import GlobalEmbedding.Paper.SymmetricSquareMapLEval
import GlobalEmbedding.Paper.SymmetricSquareMapInverse

/-! Quantitative transport on the SAME covector kernel and the original
Hilbert tensor quotient norm. The loss is the squared norm of the genuine
coordinate-to-tangent differential; no auxiliary norm or normalization is used. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper Set Function
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

def round4CovectorKernelEquiv (A : D ≃L[ℝ] E) (xi : D →L[ℝ] ℝ) :
    xi.ker ≃L[ℝ] (xi.comp A.symm.toContinuousLinearMap).ker :=
  ContinuousLinearEquiv.equivOfInverse
    ((A.toContinuousLinearMap.comp xi.ker.subtypeL).codRestrict
      (xi.comp A.symm.toContinuousLinearMap).ker (by
        intro v
        change xi (A.symm (A v)) = 0
        rw [A.symm_apply_apply]
        exact v.property))
    ((A.symm.toContinuousLinearMap.comp
        (xi.comp A.symm.toContinuousLinearMap).ker.subtypeL).codRestrict xi.ker (by
      intro w
      exact w.property))
    (by intro v; apply Subtype.ext; exact A.symm_apply_apply v)
    (by intro w; apply Subtype.ext; exact A.apply_symm_apply w)

theorem round4CovectorKernelEquiv_norm_le (A : D ≃L[ℝ] E) (xi : D →L[ℝ] ℝ) :
    ‖(round4CovectorKernelEquiv A xi).toContinuousLinearMap‖ ≤ ‖A.toContinuousLinearMap‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro v
  exact A.toContinuousLinearMap.le_opNorm v

theorem round4_covector_restriction_transport
    (A : D ≃L[ℝ] E) (xi : D →L[ℝ] ℝ)
    (B : SymmetricSquare D →L[ℝ] V) (T : SymmetricSquare E →L[ℝ] V)
    (hBT : B = T.comp (symmetricSquareMapL A.toContinuousLinearMap))
    (w : SymmetricSquare xi.ker) :
    covectorRestriction B xi w =
      covectorRestriction T (xi.comp A.symm.toContinuousLinearMap)
        (symmetricSquareMap (round4CovectorKernelEquiv A xi).toContinuousLinearMap w) := by
  have hc : A.toContinuousLinearMap.comp xi.ker.subtypeL =
      (xi.comp A.symm.toContinuousLinearMap).ker.subtypeL.comp
        (round4CovectorKernelEquiv A xi).toContinuousLinearMap := rfl
  rw [hBT]
  simp only [covectorRestriction, ContinuousLinearMap.comp_apply, symmetricSquareMapL_apply,
    symmetricSquareMap_comp, hc]

/-- A lower margin in original coordinate space gives a lower margin on the
actual transported tangent kernel, with the explicit inverse-chart loss. -/
theorem round4_covector_margin_coordinate_to_intrinsic
    (A : D ≃L[ℝ] E) (xi : D →L[ℝ] ℝ)
    (B : SymmetricSquare D →L[ℝ] V) (T : SymmetricSquare E →L[ℝ] V)
    (hBT : B = T.comp (symmetricSquareMapL A.toContinuousLinearMap))
    (eta C : ℝ) (heta : 0 ≤ eta) (hC : 0 < C)
    (hA : ‖A.toContinuousLinearMap‖^2 ≤ C)
    (hmargin : ∀ w : SymmetricSquare xi.ker, eta*‖w‖ ≤ ‖covectorRestriction B xi w‖)
    (w : SymmetricSquare (xi.comp A.symm.toContinuousLinearMap).ker) :
    (eta/C)*‖w‖ ≤ ‖covectorRestriction T (xi.comp A.symm.toContinuousLinearMap) w‖ := by
  let e := round4CovectorKernelEquiv A xi
  have he : ‖e.toContinuousLinearMap‖^2 ≤ C :=
    (sq_le_sq₀ (norm_nonneg e.toContinuousLinearMap) (norm_nonneg A.toContinuousLinearMap) |>.mpr
      (round4CovectorKernelEquiv_norm_le A xi)).trans hA
  have h := symmetricSquare_transport_lower_bound e.symm
    (covectorRestriction B xi).toLinearMap eta C heta hC he hmargin w
  have hi := round4_covector_restriction_transport A xi B T hBT
    (symmetricSquareMap e.symm.toContinuousLinearMap w)
  change covectorRestriction B xi (symmetricSquareMap e.symm.toContinuousLinearMap w) =
    covectorRestriction T (xi.comp A.symm.toContinuousLinearMap)
      (symmetricSquareMap e.toContinuousLinearMap (symmetricSquareMap e.symm.toContinuousLinearMap w)) at hi
  have hid : symmetricSquareMap e.toContinuousLinearMap
      (symmetricSquareMap e.symm.toContinuousLinearMap w) = w := by
    simpa only [ContinuousLinearEquiv.symm_symm] using symmetricSquareMap_symm e.symm w
  rw [hid] at hi
  exact h.trans_eq (congrArg norm hi)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round4_covector_margin_coordinate_to_intrinsic
