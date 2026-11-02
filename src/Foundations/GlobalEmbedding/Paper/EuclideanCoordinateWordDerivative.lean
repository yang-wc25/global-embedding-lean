import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Actual iterated coordinate partial derivatives on Euclidean lifts

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1), lines 388–399.
DAG node: `euclidean-coordinate-word-derivative`.
-/

namespace GlobalEmbedding.Paper

/-- Apply actual coordinate Frechet differentiation in the indicated word order.

The empty word retains the original actual function. At i::word differentiate the actual
tail derivative and evaluate at the original standard unit vector e_i. Thus the first letter
is the outermost partial. Source: genuine coordinate derivative products in (4.1). -/
noncomputable def euclideanCoordinateWordDerivative {a N : ℕ} :
    List (Fin a) → (EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)) →
      EuclideanSpace ℝ (Fin a) → EuclideanSpace ℝ (Fin N)
  | [], f => f
  | i :: word, f => fun x ↦ fderiv ℝ (euclideanCoordinateWordDerivative word f) x
      (EuclideanSpace.single i 1)

#print axioms euclideanCoordinateWordDerivative

end GlobalEmbedding.Paper
