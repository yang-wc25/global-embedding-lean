import GlobalEmbedding.Paper.EuclideanCoordinateWordDerivative
import Mathlib.Analysis.Calculus.FDeriv.Add

/-!
# Genuine coordinate word differentiation commutes with actual Euclidean translations

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1), lines 388–399.
DAG node: `euclidean-coordinate-word-translation`.
-/

namespace GlobalEmbedding.Paper

/-- Actual coordinate word differentiation commutes with every actual domain shift.

Induct on the actual coordinate word. The tail induction identifies the whole shifted tail
function; Mathlib's actual fderiv translation identity then identifies the next derivative
at the shifted point. Evaluate it on the original unit coordinate direction. This identity
also holds for the actual total fderiv convention, without an added smoothness assumption.
Source: translation-invariant coordinate products in (4.1). -/
theorem euclideanCoordinateWordDerivative_translate {a N : ℕ} (word : List (Fin a))
    (f : EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N))
    (h x : EuclideanSpace ℝ (Fin a)) :
    euclideanCoordinateWordDerivative word (fun y ↦ f (y + h)) x =
      euclideanCoordinateWordDerivative word f (x + h) := by
  induction word generalizing x with
  | nil => rfl
  | cons i word ih =>
      have heq : euclideanCoordinateWordDerivative word (fun y ↦ f (y + h)) =
          fun y ↦ euclideanCoordinateWordDerivative word f (y + h) := funext ih
      simp only [euclideanCoordinateWordDerivative, heq, fderiv_comp_add_right]

#print axioms euclideanCoordinateWordDerivative_translate

end GlobalEmbedding.Paper
