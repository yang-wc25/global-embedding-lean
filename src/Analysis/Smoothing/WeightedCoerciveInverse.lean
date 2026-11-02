import Smoothing.WeightedActualInverse
import GlobalEmbedding.Paper.CoerciveInverseBounds
import Mathlib.Analysis.Normed.Operator.Banach

/-!
# Actual inverse slow jets from a fixed coercivity reserve

The inverse value bound and invertibility are derived from the original
coercivity inequality. The same actual CLM.inverse is then estimated in every
slow weighted order, on the same open joint source/parameter domain.
-/

noncomputable section
open GlobalEmbedding.Paper Set
open scoped ContDiff

namespace GlobalEmbedding.Continuation

/-- Fixed coercivity and true slow jets supply the actual inverse field and its
uniform all-order slow bounds. The majorant has no scale or chart-count input. -/
theorem actual_coercive_inverse_slow_jets
    {D E : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    (j : ℕ) (O : Set D) (hO : IsOpen O) (P : D → E →L[ℝ] E)
    (hP : ContDiffOn ℝ ∞ P O) (c ell M : ℝ) (hc : 0 < c) (hell : 0 < ell) (hM : 0 ≤ M)
    (hcoer : ∀ x ∈ O, ∀ v : E, c * ‖v‖ ^ 2 ≤ inner ℝ v (P x v))
    (hjet : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k P x‖ ≤ M) :
    (∀ x ∈ O, (P x).IsInvertible ∧ ‖(P x).inverse‖ ≤ c⁻¹) ∧
    ContDiffOn ℝ ∞ (fun x => (P x).inverse) O ∧
    ∀ k ≤ j, ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k (fun y => (P y).inverse) x‖ ≤
        slowInverseMajorant c⁻¹ M j := by
  obtain ⟨hbase, hsmooth⟩ := coercive_inverse_smooth_bound O hO P c hc hP hcoer
  have hunit : ∀ x ∈ O, IsUnit (P x) := fun x hx =>
    (P x).isUnit_iff_bijective.mpr (hbase x hx).1.bijective
  have hval : ∀ x ∈ O, ‖Ring.inverse (P x)‖ ≤ c⁻¹ := by
    simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using fun x hx => (hbase x hx).2
  have h := actual_inverse_slow_weighted_jets j O hO P hP hunit ell c⁻¹ M hell
    (inv_nonneg.mpr hc.le) hM hval hjet
  refine ⟨hbase, hsmooth, ?_⟩
  simpa only [ContinuousLinearMap.ringInverse_eq_inverse] using h j le_rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_coercive_inverse_slow_jets
