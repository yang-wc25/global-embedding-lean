import GlobalEmbedding.Paper.PeriodicCAlphaNorm
import GlobalEmbedding.Paper.PeriodicCAlphaSupremumBounds
import GlobalEmbedding.Paper.PeriodicCAlphaPointwiseOperations

/-!
# Triangle inequality for the actual periodic Hölder formula

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-norm-triangle`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual periodic Hölder formula is subadditive for the actual pointwise vector-space sum.

Proof: each derivative supremum is subadditive by linearity of differentiation and the norm
triangle inequality. The difference of the top derivatives of a sum is the sum of the two
top derivative differences; division by a positive-distance power preserves the inequality.
Take the finite real suprema, then sum all estimates.
Source: `lem:balanced`, usual periodic Hölder norm expansion. -/
theorem periodicCAlphaNorm_triangle {a N k : ℕ} {α : ℝ}
    (f g : PeriodicCAlphaFunction a N k α) :
    periodicCAlphaNorm (f + g) ≤ periodicCAlphaNorm f + periodicCAlphaNorm g := by
  let D (u : PeriodicCAlphaFunction a N k α) (j : ℕ) :=
    sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j u.toFun x‖}
  let H (u : PeriodicCAlphaFunction a N k α) :=
    sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
      let d := dist
        (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
      0 < d ∧ r = ‖iteratedFDeriv ℝ k u.toFun x - iteratedFDeriv ℝ k u.toFun y‖ / d ^ α}
  have hD (u : PeriodicCAlphaFunction a N k α) (j : ℕ) : 0 ≤ D u j := by
    apply Real.sSup_nonneg
    rintro r ⟨x, hx, rfl⟩
    exact norm_nonneg _
  have hH (u : PeriodicCAlphaFunction a N k α) : 0 ≤ H u := by
    apply Real.sSup_nonneg
    rintro r ⟨x, y, hd, rfl⟩
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hd.le _)
  have hsum (j : ℕ) (hj : j ≤ k) : D (f + g) j ≤ D f j + D g j := by
    apply Real.sSup_le _ (add_nonneg (hD f j) (hD g j))
    rintro r ⟨x, hx, rfl⟩
    rw [(periodicCAlpha_pointwise_operations a N k α).2.1 f g,
      iteratedFDeriv_add_apply (f.contDiff.of_le (by exact_mod_cast hj)).contDiffAt
        (g.contDiff.of_le (by exact_mod_cast hj)).contDiffAt]
    apply (norm_add_le _ _).trans
    exact add_le_add
      (le_csSup ((periodicCAlpha_supremum_bounds f).1 j hj) ⟨x, hx, rfl⟩)
      (le_csSup ((periodicCAlpha_supremum_bounds g).1 j hj) ⟨x, hx, rfl⟩)
  have hholder : H (f + g) ≤ H f + H g := by
    apply Real.sSup_le _ (add_nonneg (hH f) (hH g))
    rintro r ⟨x, y, hd, rfl⟩
    rw [(periodicCAlpha_pointwise_operations a N k α).2.1 f g,
      iteratedFDeriv_add f.contDiff g.contDiff]
    simp only [Pi.add_apply]
    rw [add_sub_add_comm]
    calc
      _ ≤ (‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ +
          ‖iteratedFDeriv ℝ k g.toFun x - iteratedFDeriv ℝ k g.toFun y‖) / _ :=
        div_le_div_of_nonneg_right (norm_add_le _ _) (Real.rpow_nonneg hd.le _)
      _ = _ := add_div _ _ _
      _ ≤ H f + H g := add_le_add
        (le_csSup (periodicCAlpha_supremum_bounds f).2 ⟨x, y, hd, rfl⟩)
        (le_csSup (periodicCAlpha_supremum_bounds g).2 ⟨x, y, hd, rfl⟩)
  change (∑ j ∈ Finset.range (k + 1), D (f + g) j) + H (f + g) ≤
    ((∑ j ∈ Finset.range (k + 1), D f j) + H f) +
      ((∑ j ∈ Finset.range (k + 1), D g j) + H g)
  calc
    _ ≤ (∑ j ∈ Finset.range (k + 1), (D f j + D g j)) + (H f + H g) :=
      add_le_add (Finset.sum_le_sum (fun j hj ↦ hsum j (Nat.le_of_lt_succ
        (Finset.mem_range.mp hj)))) hholder
    _ = _ := by rw [Finset.sum_add_distrib]; ring

#print axioms periodicCAlphaNorm_triangle

end GlobalEmbedding.Paper
