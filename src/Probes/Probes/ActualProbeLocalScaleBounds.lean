import Probes.ActualProbeScaleBounds
import Probes.ActualProbeLocalJets

/-!
# Slow-scale remainder estimates for the original local phase/amplitude germs

These are the same explicit original sigma*tau/ell bounds, requiring C2 only
at the evaluation point. The constant is independent of phase value and scales.
-/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual cosine slow remainder has `σ τ / ell` size, under the
original slow-jet bounds. The displayed constant is independent of δ,τ,ell
and of every sine/cosine angle. -/
theorem norm_actualProbeCosRemainder_slow_scale_at
    {ψ : E → ℝ} {A : E → F} (x : E)
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x)
    (δ τ ell lam K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam) (hτell : τ ≤ ell)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hA₂ : ‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K₂ / ell ^ 2)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁)
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ P₂ / ell) :
    ‖actualProbeCosRemainder δ τ lam ψ A x‖ ≤
      (δ / τ) * (τ / ell) * (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) := by
  have hell : 0 < ell := hτ.trans_le hτell
  have h := norm_actualProbeCosRemainder_le_at hψ hA δ τ lam
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _)),
    abs_of_pos (div_pos hlam hτ)] at h
  calc
    _ ≤ (δ * τ / lam ^ 2) *
        (‖fderiv ℝ (fderiv ℝ A) x‖ +
          2 * (lam / τ) * ‖fderiv ℝ ψ x‖ * ‖fderiv ℝ A x‖ +
          (lam / τ) * ‖fderiv ℝ (fderiv ℝ ψ) x‖ * ‖A x‖) := h
    _ ≤ (δ * τ / lam ^ 2) *
        (K₂ / ell ^ 2 + 2 * (lam / τ) * P₁ * (K₁ / ell) +
          (lam / τ) * (P₂ / ell) * K₀) := by
      gcongr
    _ ≤ _ := probe_slow_scale_inequality δ τ ell lam K₀ K₁ K₂ P₁ P₂
      hδ hτ hlam hτell hK₂

/-- The sine partner obeys exactly the same scale bound and constant. -/
theorem norm_actualProbeSinRemainder_slow_scale_at
    {ψ : E → ℝ} {A : E → F} (x : E)
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x)
    (δ τ ell lam K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam) (hτell : τ ≤ ell)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hA₂ : ‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K₂ / ell ^ 2)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁)
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ P₂ / ell) :
    ‖actualProbeSinRemainder δ τ lam ψ A x‖ ≤
      (δ / τ) * (τ / ell) * (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) := by
  have hell : 0 < ell := hτ.trans_le hτell
  have h := norm_actualProbeSinRemainder_le_at hψ hA δ τ lam
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _)),
    abs_of_pos (div_pos hlam hτ)] at h
  calc
    _ ≤ (δ * τ / lam ^ 2) *
        (‖fderiv ℝ (fderiv ℝ A) x‖ +
          2 * (lam / τ) * ‖fderiv ℝ ψ x‖ * ‖fderiv ℝ A x‖ +
          (lam / τ) * ‖fderiv ℝ (fderiv ℝ ψ) x‖ * ‖A x‖) := h
    _ ≤ (δ * τ / lam ^ 2) *
        (K₂ / ell ^ 2 + 2 * (lam / τ) * P₁ * (K₁ / ell) +
          (lam / τ) * (P₂ / ell) * K₀) := by
      gcongr
    _ ≤ _ := probe_slow_scale_inequality δ τ ell lam K₀ K₁ K₂ P₁ P₂
      hδ hτ hlam hτell hK₂

#print axioms norm_actualProbeCosRemainder_slow_scale_at
#print axioms norm_actualProbeSinRemainder_slow_scale_at
end GlobalEmbedding.Offline
