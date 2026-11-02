import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateInverse
import GlobalEmbedding.Paper.LittlePeriodicCAlphaConjugationBound

/-!
# Actual translation conjugacy of a quadratic fixed equation linearization

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–425.
DAG node: `balanced-holder-quadratic-linearization-conjugacy`.
-/

namespace GlobalEmbedding.Paper

/-- An equivariant actual bounded bilinear quadratic term has conjugate linearizations.

Apply simultaneous translation equivariance to v and the inverse translate of the argument.
The actual inverse translations cancel, giving equality of bounded linear operators.
The actual translation-conjugation norm bound then preserves the factor-two norm bound.
This local-model prerequisite assumes equivariance explicitly; it does not construct the
paper-specific Q. Source: translated fixed equations and strict-smallness in `lem:balanced`. -/
theorem littlePeriodicCAlpha_quadratic_conjugation {a M N k : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a M k α)
    (hQ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (A : LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α)
    (h : EuclideanSpace ℝ (Fin a)) (v : LittlePeriodicCAlphaFunction a N k α) :
    let TX := (littlePeriodicCAlphaTranslateIsometry (N := N) (k := k) (α := α) h)
    let SX := (littlePeriodicCAlphaTranslateIsometry (N := N) (k := k) (α := α) (-h))
    let SY := (littlePeriodicCAlphaTranslateIsometry (N := M) (k := k) (α := α) (-h))
    let Ah := TX.toContinuousLinearMap.comp (A.comp SY.toContinuousLinearMap)
    Ah.comp (Q (TX v)) = TX.toContinuousLinearMap.comp
      ((A.comp (Q v)).comp SX.toContinuousLinearMap) ∧
      ‖(2 : ℝ) • Ah.comp (Q (TX v))‖ ≤ ‖(2 : ℝ) • A.comp (Q v)‖ := by
  dsimp only
  have heq : ((littlePeriodicCAlphaTranslateIsometry h).toContinuousLinearMap.comp
      (A.comp (littlePeriodicCAlphaTranslateIsometry (-h)).toContinuousLinearMap)).comp
      (Q (littlePeriodicCAlphaTranslateIsometry h v)) =
      (littlePeriodicCAlphaTranslateIsometry h).toContinuousLinearMap.comp
        ((A.comp (Q v)).comp
          (littlePeriodicCAlphaTranslateIsometry (-h)).toContinuousLinearMap) := by
    apply ContinuousLinearMap.ext
    intro w
    have hquad := hQ h v (littlePeriodicCAlphaTranslateIsometry (-h) w)
    rw [littlePeriodicCAlpha_translate_inverse] at hquad
    change littlePeriodicCAlphaTranslateIsometry h
      (A (littlePeriodicCAlphaTranslateIsometry (-h)
        (Q (littlePeriodicCAlphaTranslateIsometry h v) w))) =
      littlePeriodicCAlphaTranslateIsometry h
        (A (Q v (littlePeriodicCAlphaTranslateIsometry (-h) w)))
    rw [hquad]
    have hinv := littlePeriodicCAlpha_translate_inverse (-h)
      (Q v (littlePeriodicCAlphaTranslateIsometry (-h) w))
    rw [neg_neg] at hinv
    rw [hinv]
  refine ⟨heq, ?_⟩
  rw [heq]
  simpa only [ContinuousLinearMap.comp_smul, ContinuousLinearMap.smul_comp] using
    littlePeriodicCAlpha_conjugation_norm_le ((2 : ℝ) • A.comp (Q v)) h

#print axioms littlePeriodicCAlpha_quadratic_conjugation

end GlobalEmbedding.Paper
