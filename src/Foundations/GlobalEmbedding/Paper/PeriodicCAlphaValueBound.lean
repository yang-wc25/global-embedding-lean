import GlobalEmbedding.Paper.PeriodicCAlphaNorm
import GlobalEmbedding.Paper.PeriodicCAlphaSupremumBounds

/-!
# Pointwise value control by the actual periodic Hölder formula

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-value-bound`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual periodic Hölder formula bounds the value at every point of the Euclidean lift.

Proof: reduce each coordinate to its fractional part. Integer-lattice periodicity identifies
the value with one on the fundamental cube. The bounded zeroth derivative supremum controls
that value, and all remaining terms of the formula are nonnegative.
Source: `lem:balanced`, usual periodic Hölder norm expansion. -/
theorem periodicCAlpha_value_bound {a N k : ℕ} {α : ℝ} (f : PeriodicCAlphaFunction a N k α)
    (x : EuclideanSpace ℝ (Fin a)) : ‖f.toFun x‖ ≤ periodicCAlphaNorm f := by
  let y : EuclideanSpace ℝ (Fin a) := toLp 2 (fun i ↦ Int.fract (x i))
  have hy : ∀ i, y i ∈ Icc (0 : ℝ) 1 :=
    fun i ↦ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hxy : y + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)) = x := by
    ext i
    simp [y, Int.fract_add_floor]
  have hfxy : f.toFun x = f.toFun y := by
    simpa only [hxy] using f.periodic y (fun i ↦ ⌊x i⌋)
  rw [hfxy]
  let D : ℕ → ℝ := fun j ↦ sSup {r : ℝ | ∃ z : EuclideanSpace ℝ (Fin a),
    (∀ i, z i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j f.toFun z‖}
  have hD (j : ℕ) : 0 ≤ D j := by
    apply Real.sSup_nonneg
    rintro r ⟨z, hz, rfl⟩
    exact norm_nonneg _
  have hD0 : ‖f.toFun y‖ ≤ D 0 := by
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ)]
    exact le_csSup ((periodicCAlpha_supremum_bounds f).1 0 (Nat.zero_le _)) ⟨y, hy, rfl⟩
  have hsum : D 0 ≤ ∑ j ∈ Finset.range (k + 1), D j :=
    Finset.single_le_sum (fun j hj ↦ hD j) (by simp)
  have hhold : 0 ≤ sSup {r : ℝ | ∃ z w : EuclideanSpace ℝ (Fin a),
      let d := dist
        (toLp 2 (fun i : Fin a ↦ (z i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (w i : AddCircle (1 : ℝ))))
      0 < d ∧ r = ‖iteratedFDeriv ℝ k f.toFun z - iteratedFDeriv ℝ k f.toFun w‖ / d ^ α} := by
    apply Real.sSup_nonneg
    rintro r ⟨z, w, hd, rfl⟩
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hd) _)
  exact hD0.trans (hsum.trans (le_add_of_nonneg_right hhold))

#print axioms periodicCAlpha_value_bound

end GlobalEmbedding.Paper
