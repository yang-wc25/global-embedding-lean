import Mathlib.Analysis.Calculus.ContDiff.Bounds

/-!
# Directional derivatives contract higher derivative bounds

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 399–418; elementary bounded differentiation in the periodic Hölder spaces.
DAG node: `balanced-directional-derivative-bound`.
-/

open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Taking a fixed-direction derivative contracts both the next derivative's norm and its
pointwise differences by the norm of the direction.

Proof: differentiating evaluation at the fixed direction commutes with iterated derivatives.
The resulting multilinear map is the next derivative with the final argument fixed. Apply
its operator-norm bound, using that the product of the argument norms gains a factor `‖v‖`.
The same argument applies to the difference of the derivative tensors at two points.
Source: `lem:balanced`, bounded differentiation and translation expansion. -/
theorem directional_derivative_iterated_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (n : ℕ) (f : E → F) (hf : ContDiff ℝ (n + 1) f) (v x y : E) :
    ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z v) x‖ ≤
        ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x‖ ∧
      ‖iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z v) x -
          iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z v) y‖ ≤
        ‖v‖ * ‖iteratedFDeriv ℝ (n + 1) f x - iteratedFDeriv ℝ (n + 1) f y‖ := by
  have hdf : ContDiff ℝ n (fderiv ℝ f) := hf.fderiv_right (by norm_cast)
  constructor
  · simpa only [norm_iteratedFDeriv_fderiv] using
      norm_iteratedFDeriv_clm_apply_const (c := v) hdf.contDiffAt le_rfl
  · have hrep (z : E) (m : Fin n → E) :
        iteratedFDeriv ℝ n (fun z ↦ fderiv ℝ f z v) z m =
          iteratedFDeriv ℝ (n + 1) f z (Fin.snoc m v) := by
      rw [iteratedFDeriv_clm_apply_const_apply hdf le_rfl,
        iteratedFDeriv_succ_apply_right]
      simp
    apply ContinuousMultilinearMap.opNorm_le_bound (by positivity)
    intro m
    simp only [sub_apply, hrep]
    have h := (iteratedFDeriv ℝ (n + 1) f x -
      iteratedFDeriv ℝ (n + 1) f y).le_opNorm (Fin.snoc m v)
    simpa [Fin.prod_univ_castSucc, mul_comm, mul_left_comm, mul_assoc] using h

#print axioms directional_derivative_iterated_bound

end GlobalEmbedding.Paper
