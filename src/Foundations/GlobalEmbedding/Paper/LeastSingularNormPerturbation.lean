import GlobalEmbedding.Paper.LeastSingularNormAttainment

namespace GlobalEmbedding.Paper

/-- The actual least singular norm is 1-Lipschitz in the actual operator norm.

Proof: evaluate S at a unit minimizing vector for T. The triangle inequality
and operator difference norm bound give the one-sided estimate. Swap the maps
and combine the inequalities. Source: `defn:phase` and `prop:initialization`,
phase margin stability under operator perturbations. -/
theorem least_singular_norm_perturbation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F] :
    (∀ S T : E →L[ℝ] F,
      |leastSingularNorm S - leastSingularNorm T| ≤ ‖S - T‖) ∧
    LipschitzWith 1 (leastSingularNorm (E := E) (F := F)) ∧
    Continuous (leastSingularNorm (E := E) (F := F)) := by
  have hone : ∀ S T : E →L[ℝ] F,
      leastSingularNorm S ≤ leastSingularNorm T + ‖S - T‖ := by
    intro S T
    obtain ⟨z, hz, hval⟩ := (least_singular_norm_attainment T).1
    have hS := (least_singular_norm_bound S).2.1 z
    have herr := (S - T).le_opNorm z
    have he : ‖S z‖ ≤ ‖T z‖ + ‖(S - T) z‖ := by
      have h := norm_add_le (T z) ((S - T) z)
      simpa only [sub_apply, add_sub_cancel] using h
    rw [hz, mul_one] at hS herr
    rw [hval] at he
    linarith
  have habs : ∀ S T : E →L[ℝ] F,
      |leastSingularNorm S - leastSingularNorm T| ≤ ‖S - T‖ := by
    intro S T
    have h1 := hone S T
    have h2 := hone T S
    rw [norm_sub_rev] at h2
    exact abs_le.mpr ⟨by linarith, by linarith⟩
  have hLip : LipschitzWith 1 (leastSingularNorm (E := E) (F := F)) := by
    apply LipschitzWith.of_dist_le_mul
    intro S T
    simpa only [Real.dist_eq, dist_eq_norm, Real.norm_eq_abs, NNReal.coe_one, one_mul] using habs S T
  exact ⟨habs, hLip, hLip.continuous⟩

end GlobalEmbedding.Paper
