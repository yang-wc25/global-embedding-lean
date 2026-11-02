import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianDenseRange
import GlobalEmbedding.Paper.LittlePeriodicShiftedLaplacianTranslation
import GlobalEmbedding.Paper.LittlePeriodicCAlphaComplete
import Mathlib.Analysis.Normed.Operator.Banach

open scoped ContDiff NNReal

namespace GlobalEmbedding.Paper

/-- A genuine uniform estimate for the original shifted Laplacian yields its actual
bounded inverse, with the same constant, preserving smoothness and commuting with translations.
The true estimate makes the actual CLM antilipschitz, so its range is closed by completeness
of the original little source. Its independently proved dense range gives surjectivity.
Invert the actual CLM using Mathlib's bounded inverse theorem. The original estimate gives
the inverse bound; genuine smooth solvability and translation commutation, with uniqueness,
give the final two properties. The estimate hypothesis is explicitly retained here and is
discharged separately by the true periodic Schauder estimate.
Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced` proof. -/
theorem littlePeriodic_shiftedLaplacian_inverse_of_estimate
    {a N : ℕ} {α : ℝ} (hα : α ≤ 1) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ u : LittlePeriodicCAlphaFunction a N 2 α,
      ‖u‖ ≤ C * ‖littlePeriodicCAlphaShiftedLaplacian hα u‖) :
    ∃ W : LittlePeriodicCAlphaFunction a N 0 α →L[ℝ]
        LittlePeriodicCAlphaFunction a N 2 α,
      (∀ u, W (littlePeriodicCAlphaShiftedLaplacian hα u) = u) ∧
      (∀ f, littlePeriodicCAlphaShiftedLaplacian hα (W f) = f) ∧
      (∀ f, ‖W f‖ ≤ C * ‖f‖) ∧
      (∀ f, ContDiff ℝ ∞ f.val.toFun → ContDiff ℝ ∞ (W f).val.toFun) ∧
      ∀ h f, W (littlePeriodicCAlphaTorusTranslate h f) =
        littlePeriodicCAlphaTorusTranslate h (W f) := by
  let L := littlePeriodicCAlphaShiftedLaplacian (a := a) (N := N) hα
  have ha : AntilipschitzWith (⟨C, hC⟩ : ℝ≥0) L := L.antilipschitz_of_bound hbound
  have hc : IsClosed (Set.range L) := ha.isClosed_range L.uniformContinuous
  have hd : DenseRange L := littlePeriodic_shiftedLaplacian_denseRange hα
  have hr : Set.range L = Set.univ := by
    rw [← hc.closure_eq]
    exact hd.closure_eq
  have hs : Function.Surjective L := Set.range_eq_univ.mp hr
  let e := ContinuousLinearEquiv.ofBijective L
    (LinearMap.ker_eq_bot.mpr ha.injective) (LinearMap.range_eq_top.mpr hs)
  have hl (f) : L (e.symm f) = f := by
    change e (e.symm f) = f
    exact e.apply_symm_apply f
  refine ⟨e.symm.toContinuousLinearMap, ?_, ?_, ?_, ?_, ?_⟩
  · intro u
    change e.symm (e u) = u
    exact e.symm_apply_apply u
  · exact hl
  · intro f
    change ‖e.symm f‖ ≤ C * ‖f‖
    calc
      ‖e.symm f‖ ≤ C * ‖L (e.symm f)‖ := hbound _
      _ = C * ‖f‖ := by rw [hl]
  · intro f hf
    obtain ⟨u, hu, hLu⟩ := littlePeriodic_shiftedLaplacian_smooth_surjectivity hα f hf
    have huf : e.symm f = u := ha.injective ((hl f).trans hLu.symm)
    change ContDiff ℝ ∞ (e.symm f).val.toFun
    rw [huf]
    exact hu
  · intro h f
    apply ha.injective
    change L (e.symm (littlePeriodicCAlphaTorusTranslate h f)) =
      L (littlePeriodicCAlphaTorusTranslate h (e.symm f))
    rw [hl, littlePeriodic_shiftedLaplacian_translate, hl]

#print axioms littlePeriodic_shiftedLaplacian_inverse_of_estimate

end GlobalEmbedding.Paper
