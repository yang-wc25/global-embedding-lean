import GlobalEmbedding.Paper.LeastSingularNorm
import Mathlib.Analysis.Normed.Module.RCLike.Real

namespace GlobalEmbedding.Paper

/-- The actual unit-sphere infimum is precisely the greatest homogeneous lower
bound of the operator. No finite-dimensionality or compactness is assumed here.

Proof: the norm image is bounded below by zero and the unit sphere is nonempty.
The infimum bounds each unit output; normalize a nonzero vector to obtain the
homogeneous inequality. Conversely restrict any homogeneous lower bound to the
unit sphere and apply its greatest-lower-bound property.
Source: `defn:phase`, minimum singular value. -/
theorem least_singular_norm_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : E →L[ℝ] F) :
    0 ≤ leastSingularNorm S ∧
    (∀ z, leastSingularNorm S * ‖z‖ ≤ ‖S z‖) ∧
    (∀ m : ℝ, m ≤ leastSingularNorm S ↔ ∀ z, m * ‖z‖ ≤ ‖S z‖) := by
  let V := (fun z : E ↦ ‖S z‖) '' Metric.sphere (0 : E) 1
  have hV : V.Nonempty := (NormedSpace.sphere_nonempty (E := E).mpr (by norm_num)).image _
  have hbdd : BddBelow V := ⟨0, by rintro _ ⟨z, _, rfl⟩; exact norm_nonneg _⟩
  have hzero : 0 ≤ leastSingularNorm S := by
    apply le_csInf hV
    rintro _ ⟨z, _, rfl⟩
    exact norm_nonneg _
  have hunit : ∀ z : E, ‖z‖ = 1 → leastSingularNorm S ≤ ‖S z‖ := by
    intro z hz
    exact csInf_le hbdd ⟨z, by simpa [Metric.mem_sphere, dist_zero_right] using hz, rfl⟩
  have hlower : ∀ z, leastSingularNorm S * ‖z‖ ≤ ‖S z‖ := by
    intro z
    by_cases hz : z = 0
    · simp [hz]
    have hn : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hu : ‖(‖z‖⁻¹ : ℝ) • z‖ = 1 := by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']
    have he := hunit ((‖z‖⁻¹ : ℝ) • z) hu
    rw [map_smul, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)] at he
    calc
      _ ≤ (‖z‖⁻¹ * ‖S z‖) * ‖z‖ := mul_le_mul_of_nonneg_right he hn.le
      _ = (‖z‖⁻¹ * ‖z‖) * ‖S z‖ := by ring
      _ = _ := by rw [inv_mul_cancel₀ hn.ne', one_mul]
  refine ⟨hzero, hlower, ?_⟩
  intro m
  constructor
  · intro hm z
    exact (mul_le_mul_of_nonneg_right hm (norm_nonneg z)).trans (hlower z)
  · intro hm
    apply le_csInf hV
    rintro _ ⟨z, hz, rfl⟩
    have hzn : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
    simpa [hzn] using hm z

end GlobalEmbedding.Paper
