import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate

/-!
# Actual lifted little Hölder translations cancel with their inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–425.
DAG node: `balanced-holder-translation-inverse`.
-/

namespace GlobalEmbedding.Paper

/-- Actual translation by h after translation by −h is identity on the original little space.

The actual underlying lift is f(x+h−h)=f(x); subtype and raw carrier extensionality give
identity of the actual elements. Replacing h by −h gives cancellation in the other order.
Source: translation-conjugated fixed equations in `lem:balanced`. -/
theorem littlePeriodicCAlpha_translate_inverse {a N k : ℕ} {α : ℝ}
    (h : EuclideanSpace ℝ (Fin a)) (f : LittlePeriodicCAlphaFunction a N k α) :
    littlePeriodicCAlphaTranslateIsometry h
      (littlePeriodicCAlphaTranslateIsometry (-h) f) = f := by
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  change f.val.toFun (x + h + -h) = f.val.toFun x
  simp

#print axioms littlePeriodicCAlpha_translate_inverse

end GlobalEmbedding.Paper
