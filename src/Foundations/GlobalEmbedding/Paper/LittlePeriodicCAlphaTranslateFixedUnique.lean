import GlobalEmbedding.Paper.BalancedFixedSmallUnique
import GlobalEmbedding.Paper.LittlePeriodicCAlphaComplete
import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateFixedEquation
import GlobalEmbedding.Paper.LittlePeriodicCAlphaQuadraticConjugation

/-!
# Uniqueness under actual translated fixed equations

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-holder-translation-fixed-unique`.
-/

namespace GlobalEmbedding.Paper

/-- Two strictly small solutions of translation-related actual quadratic equations agree.

The actual translated original solution satisfies the conjugated equation. Its strict bound
is preserved by the actual quadratic linearization conjugacy. Apply the proved strict fixed
point uniqueness to it and the given other solution. This is the pointwise overlap mechanism;
actual bundle chart transitions are separate data. Source: uniqueness on overlapping fiber
charts at the end of the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_translate_fixed_unique {a M N k : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a M k α)
    (hQsym : ∀ v w, Q v w = Q w v)
    (hQτ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (A : LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α)
    (f v w : LittlePeriodicCAlphaFunction a N k α) (h : EuclideanSpace ℝ (Fin a))
    (hv : v = f + A (Q v v))
    (hsv : ‖(2 : ℝ) • A.comp (Q v)‖ < 1) :
    let TX := littlePeriodicCAlphaTranslateIsometry (N := N) (k := k) (α := α) h
    let SY := littlePeriodicCAlphaTranslateIsometry (N := M) (k := k) (α := α) (-h)
    let Ah := TX.toContinuousLinearMap.comp (A.comp SY.toContinuousLinearMap)
    w = TX f + Ah (Q w w) → ‖(2 : ℝ) • Ah.comp (Q w)‖ < 1 → w = TX v := by
  dsimp only
  intro hw hsw
  exact balanced_fixed_small_unique Q hQsym
    ((littlePeriodicCAlphaTranslateIsometry h).toContinuousLinearMap.comp
      (A.comp (littlePeriodicCAlphaTranslateIsometry (-h)).toContinuousLinearMap))
    (littlePeriodicCAlphaTranslateIsometry h f) w (littlePeriodicCAlphaTranslateIsometry h v)
    hw (littlePeriodicCAlpha_translate_fixed_equation Q hQτ A f v h hv) hsw
    ((littlePeriodicCAlpha_quadratic_conjugation Q hQτ A h v).2.trans_lt hsv)

#print axioms littlePeriodicCAlpha_translate_fixed_unique

end GlobalEmbedding.Paper
