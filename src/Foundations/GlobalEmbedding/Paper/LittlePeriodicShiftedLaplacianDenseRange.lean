import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianSmoothSurjectivity
import GlobalEmbedding.Paper.LittlePeriodicCAlphaSmoothDense

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual original shifted Laplacian has dense range in the actual original
little Holder target. Every genuinely smooth target has an actual little preimage
by the proved periodic PDE construction. The genuinely smooth subset is dense in the
actual little closure, so the actual range is dense. No inverse estimate is assumed. -/
theorem littlePeriodic_shiftedLaplacian_denseRange
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1) :
    DenseRange (littlePeriodicCAlphaShiftedLaplacian (a := a) (N := N) hα) := by
  change Dense (Set.range (littlePeriodicCAlphaShiftedLaplacian (a := a) (N := N) hα))
  refine Dense.mono (s₁ := {f : LittlePeriodicCAlphaFunction a N 0 α |
    ContDiff ℝ ∞ f.val.toFun}) ?_ (littlePeriodicCAlpha_smooth_dense a N 0 α)
  intro f hf
  obtain ⟨u, _, hu⟩ := littlePeriodic_shiftedLaplacian_smooth_surjectivity hα f hf
  exact ⟨u, hu⟩

#print axioms littlePeriodic_shiftedLaplacian_denseRange

end GlobalEmbedding.Paper
