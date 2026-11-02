import Initialization.Phase.CoefficientKernel
import GlobalEmbedding.Paper.CovectorRestriction
import GlobalEmbedding.Paper.SymmetricSquareMapComposition
import GlobalEmbedding.Paper.PhaseStabilityTransportUniform

/-!
# Actual second-form restriction under the coframe

The old phase-stability theorem assumes an exact identification of the ideal
restricted second form with a transported selector form.  This file proves
that identification for the canonical pullback on the original symmetric-square
quotient and the actual kernel equivalence constructed from the coefficient map.
It also derives the required inverse bound from the same coefficient inverse.
-/

open GlobalEmbedding.Paper
open scoped TensorProduct

noncomputable section

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance restrictionTransportRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance restrictionTransportSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E F V : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [FiniteDimensional ℝ F] [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Canonical symmetric-square pullback and restriction commute for the
literal normalized pullback covector and the literal kernel equivalence. -/
theorem covectorRestriction_coefficient_pullback
    (c : E ≃L[ℝ] F) (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0)
    (Q : SymmetricSquare F →L[ℝ] V) :
    covectorRestriction (Q.comp (symmetricSquareMapL c.toContinuousLinearMap))
      (unitCoefficientCovector c ξ) =
      (covectorRestriction Q ξ).comp
        (symmetricSquareMapL (unitCoefficientKernelEquiv c ξ hξ).toContinuousLinearMap) := by
  have hc : c.toContinuousLinearMap.comp (unitCoefficientCovector c ξ).ker.subtypeL =
      ξ.ker.subtypeL.comp (unitCoefficientKernelEquiv c ξ hξ).toContinuousLinearMap := by
    ext v
    rfl
  ext z
  simp only [covectorRestriction, ContinuousLinearMap.comp_apply, symmetricSquareMapL_apply]
  rw [symmetricSquareMap_comp, symmetricSquareMap_comp, hc]

/-- The selector's homogeneous lower bound transports with the same actual
coframe inverse reserve.  A separate kernel isomorphism or its norm is not an input. -/
theorem coefficient_pullback_restricted_lower_bound
    (c : E ≃L[ℝ] F) (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0)
    (Q : SymmetricSquare F →L[ℝ] V) (m L : ℝ) (hm : 0 < m)
    (hc : ‖c.symm.toContinuousLinearMap‖ ≤ L)
    (hQ : ∀ z, m * ‖z‖ ≤ ‖covectorRestriction Q ξ z‖)
    (z : SymmetricSquare (unitCoefficientCovector c ξ).ker) :
    (m / (1 + L ^ 2)) * ‖z‖ ≤
      ‖covectorRestriction (Q.comp (symmetricSquareMapL c.toContinuousLinearMap))
        (unitCoefficientCovector c ξ) z‖ := by
  let e := unitCoefficientKernelEquiv c ξ hξ
  have he : ‖e.symm.toContinuousLinearMap‖ ≤ L :=
    (unitCoefficientKernelEquiv_inverse_norm_le c ξ hξ).trans hc
  have hpositive : 0 < m / (2 * (1 + L ^ 2)) := by positivity
  have herr : ‖(covectorRestriction Q ξ).comp (symmetricSquareMapL e.toContinuousLinearMap) -
      (covectorRestriction Q ξ).comp (symmetricSquareMapL e.toContinuousLinearMap)‖ <
        m / (2 * (1 + L ^ 2)) := by simpa using hpositive
  have h := (phase_stability_transport_uniform_lower_bound e (covectorRestriction Q ξ)
    ((covectorRestriction Q ξ).comp (symmetricSquareMapL e.toContinuousLinearMap))
    m L hm he hQ herr).1 z
  rw [covectorRestriction_coefficient_pullback c ξ hξ Q]
  simpa only [ContinuousLinearMap.comp_apply, symmetricSquareMapL_apply, e] using h

/-- With the coframe-induced identification already proved, an actual operator
perturbation of the restricted form retains a fixed positive half-margin. -/
theorem coefficient_pullback_restricted_perturbation
    (c : E ≃L[ℝ] F) (ξ : F →L[ℝ] ℝ) (hξ : ξ ≠ 0)
    (Q : SymmetricSquare F →L[ℝ] V)
    (Q' : SymmetricSquare (unitCoefficientCovector c ξ).ker →L[ℝ] V)
    (m L : ℝ) (hm : 0 < m) (hc : ‖c.symm.toContinuousLinearMap‖ ≤ L)
    (hQ : ∀ z, m * ‖z‖ ≤ ‖covectorRestriction Q ξ z‖)
    (herr : ‖Q' - covectorRestriction
        (Q.comp (symmetricSquareMapL c.toContinuousLinearMap)) (unitCoefficientCovector c ξ)‖ <
      m / (2 * (1 + L ^ 2))) :
    ∀ z, (m / (2 * (1 + L ^ 2))) * ‖z‖ ≤ ‖Q' z‖ := by
  rw [covectorRestriction_coefficient_pullback c ξ hξ Q] at herr
  exact (phase_stability_transport_uniform_lower_bound
    (unitCoefficientKernelEquiv c ξ hξ) (covectorRestriction Q ξ) Q' m L hm
    ((unitCoefficientKernelEquiv_inverse_norm_le c ξ hξ).trans hc) hQ herr).2

end GlobalEmbedding.Initialization
