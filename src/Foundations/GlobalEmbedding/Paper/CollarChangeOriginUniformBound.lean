import Mathlib.Analysis.Analytic.ChangeOrigin

/-!
# A uniform coefficient majorant over a smaller change-of-origin ball

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Local joint Taylor series need coefficient bounds uniform over a smaller
spatial neighborhood before compactness can provide a single bound on the torus slice.
-/

open scoped NNReal ENNReal

namespace GlobalEmbedding.Paper

/-- If a+ρ is strictly below the original series radius, all centers with norm at most a have
a common bound on every recentered coefficient weighted by ρ to its degree.

Source: Proposition `prop:collar`, proof lines 530–534, uniform local Taylor bounds.
The absolute double series indexing change-of-origin coefficients is summable when a+ρ is
below the original radius. Sum first at each degree and then over all degrees to obtain a
finite nonnegative majorant M. For a center with norm at most a, monotonicity of powers and
summable nonnegative series bounds its coefficient majorant by the corresponding one at a.
Multiplication by ρ to the degree and the single-term bound by the total sum give M, uniformly
in both center and degree. No completeness, positive dimension or positive a/ρ is required.
-/
theorem collar_change_origin_uniform_bound
    {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F]
    (p : FormalMultilinearSeries 𝕜 E F) (a ρ : ℝ≥0)
    (hr : ((a + ρ : ℝ≥0) : ℝ≥0∞) < p.radius) :
    ∃ M : ℝ≥0, ∀ y : E, ‖y‖₊ ≤ a → ∀ n : ℕ,
      ‖p.changeOrigin y n‖₊ * ρ ^ n ≤ M := by
  let A (n : ℕ) : ℝ≥0 :=
    ∑' s : Σ l : ℕ, {s : Finset (Fin (n + l)) // s.card = l},
      ‖p (n + s.1)‖₊ * a ^ s.1
  have ha : (a : ℝ≥0∞) < p.radius := by
    apply lt_of_le_of_lt _ hr
    exact_mod_cast (le_add_right le_rfl : a ≤ a + ρ)
  have hA (n : ℕ) := p.changeOriginSeries_summable_aux₂ ha n
  have hB : Summable (fun n : ℕ ↦ A n * ρ ^ n) := by
    simpa only [A, ← NNReal.tsum_mul_right] using
      (NNReal.summable_sigma.mp (p.changeOriginSeries_summable_aux₁ hr)).2
  refine ⟨∑' n : ℕ, A n * ρ ^ n, ?_⟩
  intro y hy n
  have hyr : (‖y‖₊ : ℝ≥0∞) < p.radius :=
    (show (‖y‖₊ : ℝ≥0∞) ≤ (a : ℝ≥0∞) by exact_mod_cast hy).trans_lt ha
  have hsmall := p.changeOriginSeries_summable_aux₂ hyr n
  have hmajor : ‖p.changeOrigin y n‖₊ ≤ A n := by
    apply (p.nnnorm_changeOrigin_le n hyr).trans
    apply hsmall.tsum_le_tsum _ (hA n)
    intro s
    exact mul_le_mul_of_nonneg_left (pow_le_pow_left' hy s.1) zero_le
  exact (mul_le_mul_of_nonneg_right hmajor zero_le).trans (hB.le_tsum' n)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_change_origin_uniform_bound
