import GlobalEmbedding.Paper.LittlePeriodicCAlphaTranslate
import GlobalEmbedding.Paper.HilbertSchmidtCoordinateEvaluation

/-!
# Actual torus-shift conjugation is multiplication by translated coefficients

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 417–418.
DAG node: `balanced-holder-multiplier-translation-conjugacy`.
-/

namespace GlobalEmbedding.Paper

/-- Conjugating an actual pointwise multiplier by the actual little Hölder shifts equals the
multiplier associated to the shifted coefficient.

Evaluate both actual continuous linear operators at each original carrier lift point. The
pointwise multiplier formula and actual shift values give A(x+h)u(x+h−h)=A(x+h)u(x).
Operator, subtype and carrier extensionality give equality of the actual operators.
Source: translated coefficient data in the proof of `lem:balanced`. -/
theorem littlePeriodicCAlpha_multiplier_translate {a M N k : ℕ} {α : ℝ}
    (mult : LittlePeriodicCAlphaFunction a (N * M) k α →L[ℝ]
      LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α)
    (hmult : ∀ (A : LittlePeriodicCAlphaFunction a (N * M) k α)
      (u : LittlePeriodicCAlphaFunction a M k α) (x : EuclideanSpace ℝ (Fin a)),
      (mult A u).val.toFun x =
        hilbertSchmidtCoordinateEvaluation M N (A.val.toFun x) (u.val.toFun x))
    (A : LittlePeriodicCAlphaFunction a (N * M) k α) (h : EuclideanSpace ℝ (Fin a)) :
    (littlePeriodicCAlphaTranslateIsometry
      (N := N) (k := k) (α := α) h).toContinuousLinearMap.comp
      ((mult A).comp
        (littlePeriodicCAlphaTranslateIsometry
          (N := M) (k := k) (α := α) (-h)).toContinuousLinearMap) =
      mult (littlePeriodicCAlphaTranslateIsometry h A) := by
  apply ContinuousLinearMap.ext
  intro u
  apply Subtype.ext
  apply periodicCAlpha_toFun_injective
  funext x
  change (mult A (littlePeriodicCAlphaTranslateIsometry (-h) u)).val.toFun (x + h) =
    (mult (littlePeriodicCAlphaTranslateIsometry h A) u).val.toFun x
  rw [hmult, hmult]
  change hilbertSchmidtCoordinateEvaluation M N (A.val.toFun (x + h))
    (u.val.toFun (x + h + -h)) =
    hilbertSchmidtCoordinateEvaluation M N (A.val.toFun (x + h)) (u.val.toFun x)
  simp

#print axioms littlePeriodicCAlpha_multiplier_translate

end GlobalEmbedding.Paper
