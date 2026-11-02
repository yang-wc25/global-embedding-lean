import GlobalEmbedding.Paper.EuclideanPeriodicSmoothResolvent
import GlobalEmbedding.Paper.SmoothPeriodicLittleMembership
import GlobalEmbedding.Paper.LittlePeriodicCAlphaShiftedLaplacianLift

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual original shifted-Laplacian CLM has an actual smooth little-space
preimage for each genuinely smooth little-space forcing. The genuine smooth periodic
solution belongs to the original little closure by actual smooth membership; the exact
lift formula identifies its image. No a-priori estimate or abstract inverse is assumed. -/
theorem littlePeriodic_shiftedLaplacian_smooth_surjectivity
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1)
    (f : LittlePeriodicCAlphaFunction a N 0 α) (hf : ContDiff ℝ ∞ f.val.toFun) :
    ∃ u : LittlePeriodicCAlphaFunction a N 2 α,
      ContDiff ℝ ∞ u.val.toFun ∧ littlePeriodicCAlphaShiftedLaplacian hα u = f := by
  obtain ⟨u, hu, hp, he⟩ :=
    exists_euclidean_periodic_smooth_resolvent f.val.toFun hf f.val.periodic
  obtain ⟨g, hg⟩ := smooth_periodic_little_membership u hu hp hα 2
  refine ⟨g, ?_, ?_⟩
  · rw [hg]
    exact hu
  · apply Subtype.ext
    apply periodicCAlpha_toFun_injective
    funext x
    rw [littlePeriodicCAlphaShiftedLaplacian_lift, hg]
    exact he x

#print axioms littlePeriodic_shiftedLaplacian_smooth_surjectivity

end GlobalEmbedding.Paper
