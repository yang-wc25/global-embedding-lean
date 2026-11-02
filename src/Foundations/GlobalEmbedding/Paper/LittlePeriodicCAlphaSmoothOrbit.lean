import GlobalEmbedding.Paper.PeriodicCAlphaSmoothTranslateBound
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate

/-!
# Continuous actual little-Hölder translation orbits of smooth lifts

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-smooth-translation-continuity`.
-/

open scoped ContDiff NNReal

namespace GlobalEmbedding.Paper

/-- Every actual smooth little Hölder element has a continuous Euclidean-shift orbit.

Proof: the full norm bound for τ_h f−f, combined with the actual isometries and the
translation composition formula, gives a global Lipschitz constant for this orbit.
Source: smooth approximation step for little Hölder translation in `lem:balanced`. -/
theorem littlePeriodicCAlpha_smooth_orbit_continuous {a N k : ℕ} {α : ℝ}
    (f : LittlePeriodicCAlphaFunction a N k α)
    (hf : ContDiff ℝ ∞ f.val.toFun) (hα : α ≤ 1) :
    Continuous (fun h : EuclideanSpace ℝ (Fin a) ↦ littlePeriodicCAlphaTranslateIsometry h f) := by
  obtain ⟨C, hC, hbound⟩ := periodicCAlpha_smooth_translate_bound f.val hf hα
  have hlip : LipschitzWith (⟨C, hC⟩ : ℝ≥0)
      (fun h : EuclideanSpace ℝ (Fin a) ↦ littlePeriodicCAlphaTranslateIsometry h f) := by
    apply LipschitzWith.of_dist_le_mul
    intro h h'
    have hcomp : littlePeriodicCAlphaTranslateIsometry h f =
        littlePeriodicCAlphaTranslateIsometry h'
          (littlePeriodicCAlphaTranslateIsometry (h - h') f) := by
      apply Subtype.ext
      apply periodicCAlpha_toFun_injective
      funext x
      change f.val.toFun (x + h) = f.val.toFun (x + h' + (h - h'))
      congr 1
      abel
    calc
      _ = dist (littlePeriodicCAlphaTranslateIsometry h'
            (littlePeriodicCAlphaTranslateIsometry (h - h') f))
          (littlePeriodicCAlphaTranslateIsometry h' f) := by rw [← hcomp]
      _ = dist (littlePeriodicCAlphaTranslateIsometry (h - h') f) f :=
        (littlePeriodicCAlphaTranslateIsometry h').isometry.dist_eq _ _
      _ = ‖periodicCAlphaTranslate (h - h') f.val - f.val‖ := by rw [dist_eq_norm]; rfl
      _ ≤ C * ‖h - h'‖ := hbound (h - h')
      _ = _ := by rw [dist_eq_norm]; rfl
  exact hlip.continuous

#print axioms littlePeriodicCAlpha_smooth_orbit_continuous

end GlobalEmbedding.Paper
