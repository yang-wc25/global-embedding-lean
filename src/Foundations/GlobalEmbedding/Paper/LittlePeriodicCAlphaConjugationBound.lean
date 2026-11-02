import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate

/-!
# Operator-norm control of actual little Hölder translation conjugation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–425.
DAG node: `balanced-holder-translation-conjugation-bound`.
-/

namespace GlobalEmbedding.Paper

/-- Conjugation by actual little Hölder translations does not increase an operator norm.

Both constructed translations preserve the original norm. Evaluate the conjugated operator,
use its original operator bound, and take the operator norm. No nontrivial-space or nonzero
operator-norm-of-identity hypothesis is needed. Source: strict-smallness preservation in
`lem:balanced`. -/
theorem littlePeriodicCAlpha_conjugation_norm_le {a M N k : ℕ} {α : ℝ}
    (L : LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α)
    (h : EuclideanSpace ℝ (Fin a)) :
    ‖(littlePeriodicCAlphaTranslateIsometry (N := N) (k := k) (α := α) h).toContinuousLinearMap.comp
      (L.comp (littlePeriodicCAlphaTranslateIsometry
        (N := M) (k := k) (α := α) (-h)).toContinuousLinearMap)‖ ≤ ‖L‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg L)
  intro u
  change ‖littlePeriodicCAlphaTranslateIsometry h
    (L (littlePeriodicCAlphaTranslateIsometry (-h) u))‖ ≤ ‖L‖ * ‖u‖
  rw [(littlePeriodicCAlphaTranslateIsometry h).norm_map]
  exact (L.le_opNorm (littlePeriodicCAlphaTranslateIsometry (-h) u)).trans_eq
    (by rw [(littlePeriodicCAlphaTranslateIsometry (-h)).norm_map])

#print axioms littlePeriodicCAlpha_conjugation_norm_le

end GlobalEmbedding.Paper
