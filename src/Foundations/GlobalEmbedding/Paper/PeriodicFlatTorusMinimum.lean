import GlobalEmbedding.Paper.PeriodicFlatTorusDistance

/-!
# The quotient minimum for flat torus distances

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382, verification of the flat metric used in the Hölder carrier.
DAG node: `balanced-holder-flat-torus-distance-minimum`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- The L2 quotient-circle distance is the minimum Euclidean distance over all integer
lattice representatives. The minimum is attained by coordinate nearest-integer rounding.

Proof: choose the integer vector whose coordinates round the difference of the lifts. The
flat-distance formula identifies its norm with the torus distance. For every other integer
vector, the nearest-integer inequality holds in each coordinate; square and sum these
nonnegative inequalities and take square roots to obtain the asserted minimum.
Source: `lem:balanced`, periodic Hölder ambient-metric expansion. -/
theorem periodic_flat_torus_distance_minimum {a : ℕ}
    (x y : EuclideanSpace ℝ (Fin a)) :
    ∃ n : Fin a → ℤ,
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) =
        ‖x - y - toLp 2 (fun i ↦ (n i : ℝ))‖ ∧
      ∀ m : Fin a → ℤ,
        dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
            (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤
          ‖x - y - toLp 2 (fun i ↦ (m i : ℝ))‖ := by
  refine ⟨fun i ↦ round (x i - y i), ?_, ?_⟩
  · rw [periodic_flat_torus_distance]
    congr 1
  · intro m
    rw [periodic_flat_torus_distance, PiLp.norm_eq_of_L2, PiLp.norm_eq_of_L2]
    apply Real.sqrt_le_sqrt
    apply Finset.sum_le_sum
    intro i hi
    simp only [PiLp.sub_apply, Real.norm_eq_abs]
    exact pow_le_pow_left₀ (abs_nonneg _) (round_le (x i - y i) (m i)) 2

#print axioms periodic_flat_torus_distance_minimum

end GlobalEmbedding.Paper
