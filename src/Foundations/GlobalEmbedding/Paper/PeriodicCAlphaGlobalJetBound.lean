import GlobalEmbedding.Paper.PeriodicCAlphaNorm
import GlobalEmbedding.Paper.PeriodicCAlphaSupremumBounds

/-!
# Global jet control by the actual periodic Hölder formula

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-global-jet-bound`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Every derivative through the declared regularity order is bounded globally by the actual
periodic Hölder formula.

Proof: derivatives of a periodic lift are periodic, by the derivative identity for translation.
Reduce the point to its coordinate fractional parts. The corresponding finite derivative
supremum bounds the value on that cube, and is one nonnegative summand of the full formula.
Source: `lem:balanced`, usual periodic Hölder norm and compact-torus expansion. -/
theorem periodicCAlpha_global_jet_bound {a N k : ℕ} {α : ℝ} (f : PeriodicCAlphaFunction a N k α)
    (j : ℕ) (hj : j ≤ k) (x : EuclideanSpace ℝ (Fin a)) :
    ‖iteratedFDeriv ℝ j f.toFun x‖ ≤ periodicCAlphaNorm f := by
  let y : EuclideanSpace ℝ (Fin a) := toLp 2 (fun i ↦ Int.fract (x i))
  have hy : ∀ i, y i ∈ Icc (0 : ℝ) 1 :=
    fun i ↦ ⟨Int.fract_nonneg _, (Int.fract_lt_one _).le⟩
  have hxy : y + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)) = x := by
    ext i
    simp [y, Int.fract_add_floor]
  have hfxy : iteratedFDeriv ℝ j f.toFun x = iteratedFDeriv ℝ j f.toFun y := by
    have heq : (fun z ↦ f.toFun (z + toLp 2 (fun i ↦ (⌊x i⌋ : ℝ)))) = f.toFun :=
      funext (fun z ↦ f.periodic z (fun i ↦ ⌊x i⌋))
    have ht := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := f.toFun) j
      (toLp 2 (fun i ↦ (⌊x i⌋ : ℝ))) y
    simpa only [heq, hxy] using ht.symm
  rw [hfxy]
  let D : ℕ → ℝ := fun j ↦ sSup {r : ℝ | ∃ z : EuclideanSpace ℝ (Fin a),
    (∀ i, z i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j f.toFun z‖}
  have hD (j : ℕ) : 0 ≤ D j := by
    apply Real.sSup_nonneg
    rintro r ⟨z, hz, rfl⟩
    exact norm_nonneg _
  have hDj : ‖iteratedFDeriv ℝ j f.toFun y‖ ≤ D j :=
    le_csSup ((periodicCAlpha_supremum_bounds f).1 j hj) ⟨y, hy, rfl⟩
  have hsum : D j ≤ ∑ j ∈ Finset.range (k + 1), D j :=
    Finset.single_le_sum (fun j hj ↦ hD j) (Finset.mem_range.mpr (Nat.lt_succ_of_le hj))
  have hhold : 0 ≤ sSup {r : ℝ | ∃ z w : EuclideanSpace ℝ (Fin a),
      let d := dist
        (toLp 2 (fun i : Fin a ↦ (z i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (w i : AddCircle (1 : ℝ))))
      0 < d ∧ r = ‖iteratedFDeriv ℝ k f.toFun z - iteratedFDeriv ℝ k f.toFun w‖ / d ^ α} := by
    apply Real.sSup_nonneg
    rintro r ⟨z, w, hd, rfl⟩
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hd) _)
  exact hDj.trans (hsum.trans (le_add_of_nonneg_right hhold))

#print axioms periodicCAlpha_global_jet_bound

end GlobalEmbedding.Paper
