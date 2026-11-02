import GlobalEmbedding.Paper.LittlePeriodicCAlphaCoordinateWordDerivative

/-!
# Exact original lift values of bounded coordinate word differentiation

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1), lines 388–399.
DAG node: `balanced-holder-coordinate-word-value`.
-/

namespace GlobalEmbedding.Paper

/-- Actual bounded coordinate word differentiation has exactly the original classical lift.

The empty and singleton cases are the actual identity and directional-derivative values.
In the two-letter case actual composition differentiates the actual inner derivative lift,
which is the recursive word definition. All three equalities are actual data identities;
longer words contradict the length bound. Source: genuine derivative products in (4.1). -/
theorem littlePeriodicCAlphaCoordinateWordDerivative_value {a N : ℕ} {α : ℝ}
    (word : List (Fin a)) (hword : word.length ≤ 2)
    (f : LittlePeriodicCAlphaFunction a N 2 α) (x : EuclideanSpace ℝ (Fin a)) :
    (littlePeriodicCAlphaCoordinateWordDerivative word hword f).val.toFun x =
      euclideanCoordinateWordDerivative word f.val.toFun x := by
  match word, hword with
  | [], _ => rfl
  | [i], _ => rfl
  | [i, j], _ => rfl
  | _ :: _ :: _ :: _, hw => simp only [List.length_cons] at hw; omega

#print axioms littlePeriodicCAlphaCoordinateWordDerivative_value

end GlobalEmbedding.Paper
