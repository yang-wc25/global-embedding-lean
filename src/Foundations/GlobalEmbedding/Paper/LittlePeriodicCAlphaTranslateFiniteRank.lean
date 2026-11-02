import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateContinuous
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Actual little Hölder translations of finite-domain operators are norm-continuous

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-finite-rank-translation-continuity`.
-/

namespace GlobalEmbedding.Paper

/-- Composing an actual Euclidean-domain operator with little Hölder shifts is operator-norm
continuous. This is continuity on a fixed finite-dimensional family, rather than operator-norm
continuity of translations on the entire Hölder space.

Proof: each application is an actual continuous orbit. For a finite-dimensional domain,
Mathlib identifies continuity of continuous-linear-map families with pointwise continuity.
Source: finite parameter derivatives in the translation argument of `lem:balanced`. -/
theorem littlePeriodicCAlpha_translate_finite_rank_continuous {a N k : ℕ} {α : ℝ}
    (A : EuclideanSpace ℝ (Fin a) →L[ℝ] LittlePeriodicCAlphaFunction a N k α)
    (hα : α ≤ 1) :
    Continuous (fun u : EuclideanSpace ℝ (Fin a) ↦
      (littlePeriodicCAlphaTranslateIsometry u).toContinuousLinearMap.comp A) := by
  apply continuous_clm_apply.mpr
  intro v
  exact (littlePeriodicCAlpha_translate_joint_continuous hα).comp
    (continuous_id.prodMk continuous_const)

#print axioms littlePeriodicCAlpha_translate_finite_rank_continuous

end GlobalEmbedding.Paper
