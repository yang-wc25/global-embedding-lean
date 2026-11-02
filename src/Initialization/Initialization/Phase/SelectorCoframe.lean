import Initialization.Phase.SelectorJets
import Initialization.Phase.ProjectedJet
import Initialization.Phase.RestrictionTransport

/-!
# The actual selector model in the actual coframe

This is the producer for the exact identification used by the already accepted
initialization phase-stability theorem.  Its hyperplane, kernel equivalence and
second form are the explicit objects constructed from the same coframe and the
same selector.  The differentiated-coframe contribution is projected away by
an exact range identity.  The selector lower bound is transported in the native
Hilbert symmetric-square quotient norm, with no replacement Euclidean norm.
-/

noncomputable section
open Manifold GlobalEmbedding.Paper
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance selectorCoframeRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance selectorCoframeSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] {m N : ℕ}
  (C : Fin (m + 1) → ℕ) [∀ i, Fact (0 < C i)]
  (S : FreeHopfProduct C → EuclideanSpace ℝ (Fin N))
  (hS : ContMDiff (freeHopfModel C) 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ S)
  (hGram : ∀ z, Matrix.gram ℝ (fun i ↦ freeHopfDeriv C i S z) = 1)

/-- The full ideal second jet, including the literal derivative-of-coframe
term. The input `R` will be supplied by differentiating the actual coframe. -/
def selectorCoframeSecondJet (z : FreeHopfProduct C)
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (R : SymmetricSquare E →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    SymmetricSquare E →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (selectorIdealSecondJet C S z).comp (symmetricSquareMapL c.toContinuousLinearMap) +
    (selectorIdealFirstJet C S z).comp R

include hS hGram in
/-- The normal projection of the actual coefficient-corrected ideal jet is
exactly the pulled-back orbit Hessian of the same selector. -/
theorem selectorCoframeSecondJet_normal (z : FreeHopfProduct C)
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (R : SymmetricSquare E →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    (LinearMap.range ((selectorIdealFirstJet C S z).comp c.toContinuousLinearMap).toLinearMap)ᗮ.starProjection.comp
      (selectorCoframeSecondJet C S z c R) =
      (selectorIdealSecondJet C S z).comp (symmetricSquareMapL c.toContinuousLinearMap) := by
  rw [selectorCoframeSecondJet, coefficientSecondJet_normal_add]
  rw [← ContinuousLinearMap.comp_assoc, selectorIdealSecondJet_normal C S hS hGram]

include hGram in
/-- The normalized last coframe really identifies the actual ideal restricted
normal second form with the original selector's true old second form. -/
theorem selectorCoframe_restriction (z : FreeHopfProduct C)
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (R : SymmetricSquare E →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    covectorRestriction
      ((LinearMap.range ((selectorIdealFirstJet C S z).comp c.toContinuousLinearMap).toLinearMap)ᗮ.starProjection.comp
        (selectorCoframeSecondJet C S z c R))
      (unitCoefficientCovector c (lastCoordinateCovector m)) =
      (selectorOldSecondForm C S hS z).toContinuousLinearMap.comp
        (symmetricSquareMapL (coframeOldHyperplaneEquiv c).toContinuousLinearMap) := by
  rw [selectorCoframeSecondJet_normal C S hS hGram]
  rw [← selectorIdealSecondJet_oldCoordinates C S hS hGram z]
  ext u
  simp only [covectorRestriction, ContinuousLinearMap.comp_apply, symmetricSquareMapL_apply]
  rw [symmetricSquareMap_comp, symmetricSquareMap_comp,
    coframeOldHyperplaneEquiv_coefficient]

include hGram in
/-- The lower bound comes from the original selector's actual old second form;
the only transport reserve is the actual inverse coframe norm. -/
theorem selectorCoframe_restricted_lower_bound (z : FreeHopfProduct C)
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (R : SymmetricSquare E →L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (ε L : ℝ) (hε : 0 < ε) (hc : ‖c.symm.toContinuousLinearMap‖ ≤ L)
    (hbound : ∀ u, ε * ‖u‖ ≤ ‖selectorOldSecondForm C S hS z u‖)
    (u : SymmetricSquare (unitCoefficientCovector c (lastCoordinateCovector m)).ker) :
    (ε / (1 + L ^ 2)) * ‖u‖ ≤
      ‖covectorRestriction
        ((LinearMap.range ((selectorIdealFirstJet C S z).comp c.toContinuousLinearMap).toLinearMap)ᗮ.starProjection.comp
          (selectorCoframeSecondJet C S z c R))
        (unitCoefficientCovector c (lastCoordinateCovector m)) u‖ := by
  let e := coframeOldHyperplaneEquiv c
  let Q := (selectorOldSecondForm C S hS z).toContinuousLinearMap
  have herr : ‖Q.comp (symmetricSquareMapL e.toContinuousLinearMap) -
      Q.comp (symmetricSquareMapL e.toContinuousLinearMap)‖ < ε / (2 * (1 + L ^ 2)) := by
    simpa using (show 0 < ε / (2 * (1 + L ^ 2)) by positivity)
  have h := (phase_stability_transport_uniform_lower_bound e Q
    (Q.comp (symmetricSquareMapL e.toContinuousLinearMap)) ε L hε
    ((coframeOldHyperplaneEquiv_inverse_norm_le c).trans hc) hbound herr).1 u
  rw [selectorCoframe_restriction C S hS hGram]
  simpa only [ContinuousLinearMap.comp_apply, symmetricSquareMapL_apply, e, Q] using h

omit [∀ i, Fact (0 < C i)] in
include hGram in
/-- The actual frame has operator norm at most one, including empty domains. -/
theorem selectorIdealFirstJet_norm_le (z : FreeHopfProduct C) :
    ‖selectorIdealFirstJet C S z‖ ≤ 1 := by
  apply ContinuousLinearMap.opNorm_le_bound _ zero_le_one
  intro u
  rw [selectorIdealFirstJet, gramFrame_norm _ (hGram z), one_mul]

omit [FiniteDimensional ℝ E] in
include hGram in
/-- A reference bound for the same coefficient-corrected second jet follows
from the actual selector Hessian and the two actual coframe operators. -/
theorem selectorCoframeSecondJet_norm_le (z : FreeHopfProduct C)
    (c : E ≃L[ℝ] EuclideanSpace ℝ (Fin (m + 1)))
    (R : SymmetricSquare E →L[ℝ] EuclideanSpace ℝ (Fin (m + 1))) :
    ‖selectorCoframeSecondJet C S z c R‖ ≤
      ‖selectorIdealSecondJet C S z‖ * ‖c.toContinuousLinearMap‖ ^ 2 + ‖R‖ := by
  have hc : ‖symmetricSquareMapL c.toContinuousLinearMap‖ ≤ ‖c.toContinuousLinearMap‖ ^ 2 := by
    apply ContinuousLinearMap.opNorm_le_bound _ (sq_nonneg _)
    intro u
    simpa only [symmetricSquareMapL_apply] using symmetricSquareMap_norm_le c.toContinuousLinearMap u
  apply (norm_add_le _ _).trans
  apply add_le_add
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_left hc (norm_nonneg _))
  · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      ((mul_le_mul_of_nonneg_right (selectorIdealFirstJet_norm_le C S hGram z)
        (norm_nonneg R)).trans_eq (one_mul _))

end GlobalEmbedding.Initialization
