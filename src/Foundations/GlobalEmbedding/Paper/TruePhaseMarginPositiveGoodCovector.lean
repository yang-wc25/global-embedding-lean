import GlobalEmbedding.Paper.TruePhaseMarginGoodCovector
import GlobalEmbedding.Paper.GoodCovectorRescaling

open Bundle Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual phase margin is positive exactly when a source-good covector
exists, with no prior unit-norm condition on that covector.

Proof: one direction drops unit normalization from the attained-maximizer
criterion. In the other direction, divide the nonzero good covector by its
positive actual norm; scalar invariance preserves its actual kernel and
goodness. Apply the actual unit-good criterion. Source: `defn:phase`. -/
theorem true_phase_margin_positive_iff_good_covector
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}
    (hdim : 2 ≤ Module.finrank ℝ E) (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M) :
    0 < truePhaseMargin f hf x ↔
      ∃ ξ : TangentSpace I x →L[ℝ] ℝ, GoodCovector f hf x ξ := by
  have hunit := true_phase_margin_positive_iff_unit_good_covector hdim f hf x
  constructor
  · intro hpos
    obtain ⟨ξ, _, hgood⟩ := hunit.mp hpos
    exact ⟨ξ, hgood⟩
  · rintro ⟨ξ, hgood⟩
    have hp : 0 < ‖ξ‖ := (norm_pos_iff (a := ξ)).mpr hgood.1
    have ha : (‖ξ‖⁻¹ : ℝ) ≠ 0 := inv_ne_zero hp.ne'
    have hnorm : ‖‖ξ‖⁻¹ • ξ‖ = 1 := by
      apply le_antisymm
      · calc
          _ ≤ ‖(‖ξ‖⁻¹ : ℝ)‖ * ‖ξ‖ := ContinuousLinearMap.opNorm_smul_le ‖ξ‖⁻¹ ξ
          _ = 1 := by
            rw [Real.norm_eq_abs, abs_inv, abs_of_pos hp, inv_mul_cancel₀ hp.ne']
      · have he := ContinuousLinearMap.opNorm_smul_le ‖ξ‖ (‖ξ‖⁻¹ • ξ)
        rw [smul_inv_smul₀ hp.ne', Real.norm_eq_abs, abs_of_pos hp] at he
        exact le_of_mul_le_mul_left (by simpa only [mul_one] using he) hp
    exact hunit.mpr ⟨‖ξ‖⁻¹ • ξ, hnorm,
      (good_covector_smul_iff f hf x ξ ‖ξ‖⁻¹ ha).mpr hgood⟩

end GlobalEmbedding.Paper
