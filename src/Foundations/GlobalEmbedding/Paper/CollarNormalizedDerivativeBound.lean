import Mathlib.Analysis.Analytic.IteratedFDeriv
import Mathlib.Analysis.Complex.Basic

/-!
# Full operator-norm estimate for normalized analytic derivatives

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. Local multilinear Taylor estimates must bound the full coefficient
operator norms, rather than only their diagonal evaluations.
-/

open scoped ENNReal

namespace GlobalEmbedding.Paper

/-- The full normalized nth derivative of a genuine complex power-series sum has operator norm
at most the norm of its nth coefficient.

Source: Proposition `prop:collar`, proof lines 530–534, local uniform Taylor coefficient bounds.
The nth derivative is the sum over all permutations of the nth multilinear coefficient. Each
term is bounded by its operator norm times the product of the input norms, invariant under
permutation. There are exactly n! permutations, so the full derivative operator norm is at most
n! times the coefficient norm. Multiplication by the inverse complex factorial cancels that
factor, since n! is nonzero. Completeness is used only by Mathlib's actual power-series
derivative identity; no holomorphic-to-analytic implication or diagonal polarization is assumed.
-/
theorem collar_normalized_derivative_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
    [NormedAddCommGroup F] [NormedSpace ℂ F] [CompleteSpace F]
    {f : E → F} {p : FormalMultilinearSeries ℂ E F} {x : E} {r : ℝ≥0∞}
    (hp : HasFPowerSeriesOnBall f p x r) (n : ℕ) :
    ‖(n.factorial : ℂ)⁻¹ • iteratedFDeriv ℂ n f x‖ ≤ ‖p n‖ := by
  classical
  have hD : ‖iteratedFDeriv ℂ n f x‖ ≤ (n.factorial : ℝ) * ‖p n‖ := by
    apply (iteratedFDeriv ℂ n f x).opNorm_le_bound (by positivity)
    intro v
    rw [hp.iteratedFDeriv_eq_sum_of_completeSpace v]
    calc
      _ ≤ ∑ σ : Equiv.Perm (Fin n), ‖p n (fun i ↦ v (σ i))‖ := norm_sum_le _ _
      _ ≤ ∑ _σ : Equiv.Perm (Fin n), ‖p n‖ * ∏ i : Fin n, ‖v i‖ := by
        apply Finset.sum_le_sum
        intro σ _
        have hprod : (∏ i : Fin n, ‖v (σ i)‖) = ∏ i : Fin n, ‖v i‖ :=
          Equiv.prod_comp σ (fun i ↦ ‖v i‖)
        simpa only [hprod] using (p n).le_opNorm (fun i ↦ v (σ i))
      _ = ((n.factorial : ℝ) * ‖p n‖) * ∏ i : Fin n, ‖v i‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_perm, Fintype.card_fin,
          nsmul_eq_mul]
        ring
  have hfact : (n.factorial : ℝ) ≠ 0 := by exact_mod_cast n.factorial_ne_zero
  rw [norm_smul, norm_inv, RCLike.norm_natCast]
  calc
    _ ≤ (n.factorial : ℝ)⁻¹ * ((n.factorial : ℝ) * ‖p n‖) :=
      mul_le_mul_of_nonneg_left hD (inv_nonneg.mpr (Nat.cast_nonneg _))
    _ = ‖p n‖ := inv_mul_cancel_left₀ hfact _

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_normalized_derivative_bound
