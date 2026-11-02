import Mathlib.Analysis.InnerProductSpace.PiL2

/-!
# Faithful norm calibration of real scalars as original one-coordinate Euclidean values

Source: `literature/parallelizable-stable-plus-one/main.tex`, (4.1), lines 388–399.
DAG node: `real-euclidean-one-isometry`.
-/

namespace GlobalEmbedding.Paper

/-- The actual real scalar is linearly isometric to the original Euclidean Fin1 value model.

Use the inverse of Mathlib's actual one-coordinate PiLp linear equivalence. It maps r to
its constant one-coordinate vector. The exact Euclidean norm formula in one coordinate proves norm
preservation. Thus the scalar Holder output has its original scalar norm, not an arbitrary
coordinate model. Source: scalar derivative pairings in (4.1). -/
noncomputable def realEuclideanOneIsometry : ℝ ≃ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 1) where
  toLinearEquiv := (PiLp.equivOfUnique 2 ℝ (fun _ : Fin 1 ↦ ℝ)).symm.toLinearEquiv
  norm_map' := by
    intro r
    change ‖WithLp.toLp 2 (fun _ : Fin 1 ↦ r)‖ = ‖r‖
    rw [EuclideanSpace.norm_eq]
    simp [Real.sqrt_sq_eq_abs]

#print axioms realEuclideanOneIsometry

end GlobalEmbedding.Paper
