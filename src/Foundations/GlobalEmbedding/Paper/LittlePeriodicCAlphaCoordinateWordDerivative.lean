import GlobalEmbedding.Paper.LittlePeriodicCAlphaDirectionalDerivative
import GlobalEmbedding.Paper.EuclideanCoordinateWordDerivative

/-!
# Genuine bounded coordinate word derivatives on the original little Hölder spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1), lines 388–399.
DAG node: `balanced-holder-coordinate-word-derivative`.
-/

namespace GlobalEmbedding.Paper

/-- An at-most-two-letter coordinate word gives an actual bounded c2→c^(2−length) operator.

Empty words use the original continuous identity; singletons use actual bounded coordinate
differentiation; two-letter words compose actual bounded differentiation at orders2→1→0.
A longer word contradicts the stated length bound. Every branch is actual operator data on
the original little Hölder spaces. Source: derivative products of order at most two in (4.1). -/
noncomputable def littlePeriodicCAlphaCoordinateWordDerivative {a N : ℕ} {α : ℝ}
    (word : List (Fin a)) (hword : word.length ≤ 2) :
    LittlePeriodicCAlphaFunction a N 2 α →L[ℝ]
      LittlePeriodicCAlphaFunction a N (2 - word.length) α :=
  match word, hword with
  | [], _ => ContinuousLinearMap.id ℝ (LittlePeriodicCAlphaFunction a N 2 α)
  | [i], _ => littlePeriodicCAlphaDirectionalDerivative (k := 1) (EuclideanSpace.single i 1)
  | [i, j], _ =>
      (littlePeriodicCAlphaDirectionalDerivative (k := 0) (EuclideanSpace.single i 1)).comp
        (littlePeriodicCAlphaDirectionalDerivative (k := 1) (EuclideanSpace.single j 1))
  | _ :: _ :: _ :: _, hw => by simp only [List.length_cons] at hw; omega

#print axioms littlePeriodicCAlphaCoordinateWordDerivative

end GlobalEmbedding.Paper
