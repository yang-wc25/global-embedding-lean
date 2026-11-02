import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Norms of genuinely iterated jets

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
where Taylor's theorem is applied to an already differentiated source.
Native currying is an isometry, so the operator norm of an iterated
derivative of a jet is exactly the norm of the total-order derivative.
No finite-dimensional coordinate comparison is inserted into this
identity.
-/

open scoped ContDiff

namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The operator norm of the i-th derivative of the j-th actual jet
equals the operator norm of the actual derivative of total order i+j.
This is purely the native isometric currying identity. -/
theorem norm_iteratedFDeriv_iteratedFDeriv (u : E → F) (i j : ℕ) (x : E) :
    ‖iteratedFDeriv ℝ i (iteratedFDeriv ℝ j u) x‖ =
      ‖iteratedFDeriv ℝ (i + j) u x‖ := by
  induction j generalizing i with
  | zero =>
    rw [iteratedFDeriv_zero_eq_comp,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left, Nat.add_zero]
  | succ j ih =>
    rw [iteratedFDeriv_succ_eq_comp_left,
      LinearIsometryEquiv.norm_iteratedFDeriv_comp_left (𝕜 := ℝ)
        (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (j + 1) => E) F).symm
        (fderiv ℝ (iteratedFDeriv ℝ j u)) x i,
      norm_iteratedFDeriv_fderiv, ih]
    exact congrArg (fun a : ℕ => ‖iteratedFDeriv ℝ a u x‖) (by omega)

end GlobalEmbedding.Offline
