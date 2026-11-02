import GlobalEmbedding.Paper.PointwiseJetNormalBound
import Mathlib.Topology.Algebra.Module.Equiv.Submodule

/-!
# The derivative-of-coframe term really is tangent

Source: `prop:initialization`, second-jet comparison.  Write the ideal first jet
as `D ∘ c`, with `c` invertible, and its second jet as `Q + D ∘ R`.  The term
`D ∘ R` includes the derivatives of the coframe coefficients.  Its normal
projection vanishes because the *actual ranges* of `D ∘ c` and `D` agree.
The last theorem feeds this identity into the existing quantitative projection
estimate, so its conclusion compares with `Q`, not an assumed projected model.
-/

noncomputable section

namespace GlobalEmbedding.Initialization

variable {E F G V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup V] [InnerProductSpace ℝ V]

/-- An actual invertible coefficient change preserves the actual first-jet range. -/
theorem coefficientFirstJet_range (D : F →L[ℝ] V) (c : E ≃L[ℝ] F) :
    LinearMap.range (D.comp c.toContinuousLinearMap).toLinearMap =
      LinearMap.range D.toLinearMap := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨c u, rfl⟩
  · rintro ⟨u, rfl⟩
    refine ⟨c.symm u, ?_⟩
    simp

/-- The derivative-of-coframe contribution lies in the same ideal tangent range. -/
theorem coefficientSecondJet_tangent (D : F →L[ℝ] V) (c : E ≃L[ℝ] F)
    (R : G →L[ℝ] F) (u : G) :
    D (R u) ∈ LinearMap.range (D.comp c.toContinuousLinearMap).toLinearMap := by
  rw [coefficientFirstJet_range]
  exact ⟨R u, rfl⟩

variable [CompleteSpace V]

/-- The *whole* linear second-jet operator coming from differentiated
coefficients is killed by the true ideal orthogonal normal projection. -/
theorem coefficientSecondJet_normal_zero (D : F →L[ℝ] V) (c : E ≃L[ℝ] F)
    (R : G →L[ℝ] F) :
    (LinearMap.range (D.comp c.toContinuousLinearMap).toLinearMap)ᗮ.starProjection.comp
      (D.comp R) = 0 := by
  ext u
  exact Submodule.starProjection_orthogonal_apply_eq_zero
    (coefficientSecondJet_tangent D c R u)

/-- Removing the differentiated coefficients is an exact identity on the
original operator domain, including the symmetric-square domain used later. -/
theorem coefficientSecondJet_normal_add (D : F →L[ℝ] V) (c : E ≃L[ℝ] F)
    (R : G →L[ℝ] F) (Q : G →L[ℝ] V) :
    (LinearMap.range (D.comp c.toContinuousLinearMap).toLinearMap)ᗮ.starProjection.comp
      (Q + D.comp R) =
      (LinearMap.range D.toLinearMap)ᗮ.starProjection.comp Q := by
  rw [ContinuousLinearMap.comp_add, coefficientSecondJet_normal_zero, add_zero,
    coefficientFirstJet_range]

variable [FiniteDimensional ℝ E]

/-- The established normal-projection stability estimate applied to the
actual coefficient-corrected ideal second jet.  The raw error is measured
against `Q + D ∘ R`, while the final normal error is measured against `Q`.
No immersion of the perturbed map is assumed; its ellipticity is a conclusion. -/
theorem projected_jet_estimate_with_coframe_term
    (D : F →L[ℝ] V) (c : E ≃L[ℝ] F) (B : E →L[ℝ] V)
    (R : G →L[ℝ] F) (Q Q' : G →L[ℝ] V) (lam bound : ℝ)
    (hlam : 0 < lam)
    (hA : ∀ v, lam * ‖v‖ ^ 2 ≤ ‖D (c v)‖ ^ 2)
    (herr : ‖D.comp c.toContinuousLinearMap - B‖ ≤ Real.sqrt lam / 2)
    (hQ : ‖Q + D.comp R‖ ≤ bound) :
    (∀ v, (lam / 4) * ‖v‖ ^ 2 ≤ ‖B v‖ ^ 2) ∧
    ‖(LinearMap.range B.toLinearMap)ᗮ.starProjection.comp Q' -
        (LinearMap.range D.toLinearMap)ᗮ.starProjection.comp Q‖ ≤
      ‖Q' - (Q + D.comp R)‖ +
        (3 / Real.sqrt lam) * bound * ‖D.comp c.toContinuousLinearMap - B‖ := by
  have h := GlobalEmbedding.Paper.pointwise_projected_jet_estimate
    (D.comp c.toContinuousLinearMap) B (Q + D.comp R) Q' lam bound
    hlam hA herr hQ
  rwa [coefficientSecondJet_normal_add] at h

end GlobalEmbedding.Initialization
