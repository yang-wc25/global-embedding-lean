import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Group.AddCircle

/-!
# The flat torus distance on Euclidean lifts

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382, periodic Hölder ambient-space expansion.
DAG node: `balanced-holder-flat-torus-distance`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- The flat L2 distance modulo the integer lattice equals the Euclidean norm of the
coordinate nearest-integer representative of the difference.

Proof: expand the L2 quotient-circle distance coordinatewise. In each quotient circle,
Mathlib identifies the norm of a real class with the absolute value of its nearest-integer
remainder. Reassemble these absolute values as the Euclidean L2 norm.
Source: `lem:balanced`, periodic Hölder ambient-space expansion. -/
theorem periodic_flat_torus_distance {a : ℕ}
    (x y : EuclideanSpace ℝ (Fin a)) :
    dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) =
      ‖toLp 2 (fun i : Fin a ↦ x i - y i - (round (x i - y i) : ℝ))‖ := by
  rw [PiLp.dist_eq_sum (by norm_num), PiLp.norm_eq_sum (by norm_num)]
  congr 1
  apply Finset.sum_congr rfl
  intro i hi
  rw [dist_eq_norm]
  simp only [← AddCircle.coe_sub, AddCircle.norm_eq]
  simp

#print axioms periodic_flat_torus_distance

end GlobalEmbedding.Paper
