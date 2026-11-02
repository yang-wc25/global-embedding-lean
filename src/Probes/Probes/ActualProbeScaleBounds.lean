import Probes.ActualScaledProbe
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# The actual slow remainder at the original sigma tau / ell scale

Source: the slow-differentiation estimate following (8.3). These estimates
are derived from native first and second jets of the displayed amplitude and
phase. The parameter/fast-angle independent constant is explicit.
-/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

/-- The exact scale reduction behind the slow spatial remainder. -/
theorem probe_slow_scale_inequality
    (δ τ ell lam K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam) (hτell : τ ≤ ell)
    (hK₂ : 0 ≤ K₂) :
    (δ * τ / lam ^ 2) *
      (K₂ / ell ^ 2 + 2 * (lam / τ) * P₁ * (K₁ / ell) +
        (lam / τ) * (P₂ / ell) * K₀) ≤
    (δ / τ) * (τ / ell) * (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) := by
  have hell : 0 < ell := hτ.trans_le hτell
  have heq : (δ * τ / lam ^ 2) *
      (K₂ / ell ^ 2 + 2 * (lam / τ) * P₁ * (K₁ / ell) +
        (lam / τ) * (P₂ / ell) * K₀) =
    (δ / τ) * ((τ / ell) ^ 2 * (K₂ / lam ^ 2) +
      (τ / ell) * ((2 * P₁ * K₁ + P₂ * K₀) / lam)) := by
    field_simp
    <;> ring
  rw [heq]
  have hr0 : 0 ≤ τ / ell := (div_pos hτ hell).le
  have hr1 : τ / ell ≤ 1 := (div_le_one hell).mpr hτell
  have hr2 : (τ / ell) ^ 2 ≤ τ / ell := by nlinarith
  calc
    _ ≤ (δ / τ) * ((τ / ell) * (K₂ / lam ^ 2) +
        (τ / ell) * ((2 * P₁ * K₁ + P₂ * K₀) / lam)) := by
      apply mul_le_mul_of_nonneg_left _ (div_nonneg hδ hτ.le)
      exact add_le_add (mul_le_mul_of_nonneg_right hr2
        (div_nonneg hK₂ (sq_nonneg _))) le_rfl
    _ = _ := by ring

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual cosine slow remainder has `σ τ / ell` size, under the
original slow-jet bounds. The displayed constant is independent of δ,τ,ell
and of every sine/cosine angle. -/
theorem norm_actualProbeCosRemainder_slow_scale
    {ψ : E → ℝ} {A : E → F} (hψ : ContDiff ℝ 2 ψ) (hA : ContDiff ℝ 2 A)
    (δ τ ell lam K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam) (hτell : τ ≤ ell)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (x : E)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hA₂ : ‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K₂ / ell ^ 2)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁)
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ P₂ / ell) :
    ‖actualProbeCosRemainder δ τ lam ψ A x‖ ≤
      (δ / τ) * (τ / ell) * (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) := by
  have hell : 0 < ell := hτ.trans_le hτell
  have h := norm_actualProbeCosRemainder_le hψ hA δ τ lam x
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
theorem norm_actualProbeSinRemainder_slow_scale
    {ψ : E → ℝ} {A : E → F} (hψ : ContDiff ℝ 2 ψ) (hA : ContDiff ℝ 2 A)
    (δ τ ell lam K₀ K₁ K₂ P₁ P₂ : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam) (hτell : τ ≤ ell)
    (hK₀ : 0 ≤ K₀) (hK₁ : 0 ≤ K₁) (hK₂ : 0 ≤ K₂)
    (hP₁ : 0 ≤ P₁) (hP₂ : 0 ≤ P₂) (x : E)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hA₂ : ‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K₂ / ell ^ 2)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁)
    (hψ₂ : ‖fderiv ℝ (fderiv ℝ ψ) x‖ ≤ P₂ / ell) :
    ‖actualProbeSinRemainder δ τ lam ψ A x‖ ≤
      (δ / τ) * (τ / ell) * (K₂ / lam ^ 2 + (2 * P₁ * K₁ + P₂ * K₀) / lam) := by
  have hell : 0 < ell := hτ.trans_le hτell
  have h := norm_actualProbeSinRemainder_le hψ hA δ τ lam x
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

#print axioms probe_slow_scale_inequality
#print axioms norm_actualProbeCosRemainder_slow_scale
#print axioms norm_actualProbeSinRemainder_slow_scale
end GlobalEmbedding.Offline
