import GlobalEmbedding.Paper.CollarNormalizedDerivativeBound
import GlobalEmbedding.Paper.CollarChangeOriginUniformBound

/-!
# Uniform normalized derivative bounds on a smaller analytic ball

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Actual joint Taylor series provide derivative estimates uniform in
both spatial center and Taylor degree on smaller neighborhoods.
-/

open scoped NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- A genuine power-series expansion supplies one bound for all normalized derivative norms,
weighted by ρ to the degree, at every center in a smaller closed ball of radius a.

Source: Proposition `prop:collar`, proof lines 530–534, local uniform Taylor estimates.
The original radius contains a+ρ, so the proved uniform change-of-origin coefficient majorant
applies to its formal series. At each permitted center the actual family admits that recentered
power series. Its normalized full derivative norm is bounded by the corresponding coefficient
norm by the permutation-sum estimate. Multiplying by ρ to the degree gives the same majorant
for every center and every degree. No diagonal norm estimate is substituted for operator norm.
-/
theorem collar_uniform_normalized_derivatives
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {x : E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (a ρ : ℝ≥0)
    (hr : ((a + ρ : ℝ≥0) : ℝ≥0∞) < r) :
    ∃ M : ℝ≥0, ∀ y : E, ‖y‖₊ ≤ a → ∀ n : ℕ,
      ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n f (x + y)‖₊ * ρ ^ n ≤ M := by
  obtain ⟨M, hM⟩ := collar_change_origin_uniform_bound p a ρ (hr.trans_le hp.r_le)
  refine ⟨M, ?_⟩
  intro y hy n
  have hyr : (‖y‖₊ : ℝ≥0∞) < r := by
    apply lt_of_le_of_lt _ hr
    exact_mod_cast hy.trans (le_add_right le_rfl : a ≤ a + ρ)
  have hD : ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n f (x + y)‖₊ ≤
      ‖p.changeOrigin y n‖₊ := by
    exact_mod_cast collar_normalized_derivative_bound (hp.changeOrigin hyr) n
  exact (mul_le_mul_of_nonneg_right hD zero_le).trans (hM y hy n)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_uniform_normalized_derivatives
