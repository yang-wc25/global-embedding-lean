import Mathlib.Analysis.Normed.Operator.Basic

/-!
# First-jet lower bounds under operator perturbations

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, uniform ellipticity of the perturbed first jet.
-/

namespace GlobalEmbedding.Paper

/-- A first-jet lower bound loses at most the operator norm perturbation.

Proof: the triangle inequality gives ‖Av‖≤‖Bv‖+‖(A−B)v‖. Bound the last term
by ‖A−B‖‖v‖ and use the given lower bound. The result includes zero source spaces
and is purely pointwise, with no compactness or connectedness assumption.
Source: `prop:initialization`, retention of a fixed ellipticity margin. -/
theorem linear_map_lower_bound_perturbation
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A B : E →L[ℝ] F) (a δ : ℝ) (hA : ∀ v, a * ‖v‖ ≤ ‖A v‖)
    (herr : ‖A - B‖ ≤ δ) (v : E) :
    (a - δ) * ‖v‖ ≤ ‖B v‖ := by
  have ht : ‖A v‖ ≤ ‖B v‖ + ‖(A - B) v‖ := by
    calc
      _ = ‖B v + (A - B) v‖ := by congr 1; simp
      _ ≤ _ := norm_add_le _ _
  have hn := (A - B).le_opNorm v
  have hb := mul_le_mul_of_nonneg_right herr (norm_nonneg v)
  have hl := hA v
  nlinarith

end GlobalEmbedding.Paper
