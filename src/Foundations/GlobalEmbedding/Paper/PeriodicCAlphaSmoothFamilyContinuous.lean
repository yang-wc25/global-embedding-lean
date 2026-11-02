import GlobalEmbedding.Paper.PeriodicCAlphaFamilyContinuous
import GlobalEmbedding.Paper.SmoothSpatialJets

/-!
# Actual Hölder norm continuity from joint source smoothness

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-smooth-family-continuity`.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- An actual periodic Hölder slice family with genuinely jointly C∞ underlying lifts is
continuous in its original full Hölder norm.

Derive each slice's extra spatial regularity by fixing the parameter, and derive joint
spatial-jet continuity from source smoothness. Apply the proved actual norm family-continuity
criterion. No norm-valued continuity is assumed. Source: smooth slices in `lem:balanced`. -/
theorem periodicCAlpha_smooth_family_continuous
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [WeaklyLocallyCompactSpace P]
    {a N k : ℕ} {α : ℝ} (F : P → PeriodicCAlphaFunction a N k α)
    (hF : ContDiff ℝ ∞ (fun z : P × EuclideanSpace ℝ (Fin a) ↦ (F z.1).toFun z.2))
    (hα : α ≤ 1) : Continuous F := by
  apply periodicCAlpha_family_continuous F _ _ hα
  · intro p
    exact (hF.comp (contDiff_const.prodMk contDiff_id)).of_le (by simp)
  · intro j hj
    exact (smooth_spatial_jets (fun p ↦ (F p).toFun) hF j).continuous

#print axioms periodicCAlpha_smooth_family_continuous

end GlobalEmbedding.Paper
