import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslateInverse

/-!
# Actual translated quadratic fixed equation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-translation-fixed-equation`.
-/

namespace GlobalEmbedding.Paper

/-- Actual translation carries an equivariant quadratic fixed point to the conjugated equation.

Simultaneous translation equivariance identifies the translated quadratic term. Inverse
translation cancels it inside the conjugated coefficient; linearity then translates the
original equation. Source: translated equations in the local proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_translate_fixed_equation {a M N k : ℕ} {α : ℝ}
    (Q : LittlePeriodicCAlphaFunction a N k α →L[ℝ]
      LittlePeriodicCAlphaFunction a N k α →L[ℝ] LittlePeriodicCAlphaFunction a M k α)
    (hQ : ∀ h v w, Q (littlePeriodicCAlphaTranslateIsometry h v)
      (littlePeriodicCAlphaTranslateIsometry h w) =
        littlePeriodicCAlphaTranslateIsometry h (Q v w))
    (A : LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α)
    (f v : LittlePeriodicCAlphaFunction a N k α) (h : EuclideanSpace ℝ (Fin a))
    (hv : v = f + A (Q v v)) :
    let TX := littlePeriodicCAlphaTranslateIsometry (N := N) (k := k) (α := α) h
    let SY := littlePeriodicCAlphaTranslateIsometry (N := M) (k := k) (α := α) (-h)
    TX v = TX f + (TX.toContinuousLinearMap.comp (A.comp SY.toContinuousLinearMap))
      (Q (TX v) (TX v)) := by
  dsimp only
  change littlePeriodicCAlphaTranslateIsometry h v =
    littlePeriodicCAlphaTranslateIsometry h f + littlePeriodicCAlphaTranslateIsometry h
      (A (littlePeriodicCAlphaTranslateIsometry (-h)
        (Q (littlePeriodicCAlphaTranslateIsometry h v)
          (littlePeriodicCAlphaTranslateIsometry h v))))
  rw [hQ]
  have hinv := littlePeriodicCAlpha_translate_inverse (-h) (Q v v)
  rw [neg_neg] at hinv
  rw [hinv]
  simpa only [map_add] using congrArg (littlePeriodicCAlphaTranslateIsometry h) hv

#print axioms littlePeriodicCAlpha_translate_fixed_equation

end GlobalEmbedding.Paper
