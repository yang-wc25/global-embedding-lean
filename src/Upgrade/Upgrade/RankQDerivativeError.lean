import Mathlib.Analysis.Normed.Operator.Prod

/-! The operator-norm estimate used only AFTER fixed-weight simulation. -/
noncomputable section
namespace GlobalEmbedding.Upgrade
variable {S R V : Type*} [NormedAddCommGroup S] [NormedSpace ℝ S]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem rankQ_pair_derivative_variation_le
    (D D₀ : S →L[ℝ] R) (A : S) (v : V) (delta : ℝ)
    (hD : ‖D - D₀‖ ≤ delta) :
    ‖(D A,v) - (D₀ A,v)‖ ≤ delta * ‖A‖ := by
  have hdelta : 0 ≤ delta := (norm_nonneg (D - D₀)).trans hD
  apply norm_prod_le_iff.mpr
  constructor
  · exact (ContinuousLinearMap.le_opNorm (D - D₀) A).trans
      (mul_le_mul_of_nonneg_right hD (norm_nonneg A))
  · simpa only [Prod.snd_sub, Prod.snd, sub_self, norm_zero] using
      mul_nonneg hdelta (norm_nonneg A)
end GlobalEmbedding.Upgrade
