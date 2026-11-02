import GlobalEmbedding.Paper.LeastSingularNormBound
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.Order.Compact

namespace GlobalEmbedding.Paper

/-- On a nontrivial finite-dimensional source the actual least singular norm is
attained. It is bounded above by the operator norm and positive exactly for
injective maps.

Proof: apply the extreme value theorem to the actual norm image of the compact
unit sphere. The infimum characterizes this minimum. Injectivity makes the
minimizing image nonzero, while a positive homogeneous lower bound gives zero
kernel. Source: `defn:phase`, minimum singular value. -/
theorem least_singular_norm_attainment
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [Nontrivial E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : E →L[ℝ] F) :
    (∃ z : E, ‖z‖ = 1 ∧ ‖S z‖ = leastSingularNorm S) ∧
    leastSingularNorm S ≤ ‖S‖ ∧
    (0 < leastSingularNorm S ↔ Function.Injective S) := by
  have hne : (Metric.sphere (0 : E) 1).Nonempty :=
    NormedSpace.sphere_nonempty.mpr (by norm_num)
  obtain ⟨z, hz, hmin⟩ := (isCompact_sphere (0 : E) 1).exists_isMinOn hne
    S.continuous.norm.continuousOn
  have hz1 : ‖z‖ = 1 := by simpa [Metric.mem_sphere, dist_zero_right] using hz
  have hbound := least_singular_norm_bound S
  have hval : ‖S z‖ = leastSingularNorm S := by
    apply le_antisymm
    · apply le_csInf (hne.image (fun y : E ↦ ‖S y‖))
      rintro _ ⟨y, hy, rfl⟩
      exact hmin hy
    · simpa [hz1] using hbound.2.1 z
  have hop : leastSingularNorm S ≤ ‖S‖ := by
    rw [← hval]
    simpa [hz1] using S.le_opNorm z
  refine ⟨⟨z, hz1, hval⟩, hop, ?_⟩
  constructor
  · intro hpos
    apply (injective_iff_map_eq_zero S).mpr
    intro v hv
    have he := hbound.2.1 v
    rw [hv, norm_zero] at he
    by_contra hv0
    exact (not_lt_of_ge he) (mul_pos hpos (norm_pos_iff.mpr hv0))
  · intro hinj
    rw [← hval]
    apply norm_pos_iff.mpr
    intro he
    have hz0 : z = 0 := hinj (by simpa using he)
    simp [hz0] at hz1

end GlobalEmbedding.Paper
