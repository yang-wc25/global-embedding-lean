import GlobalEmbedding.Paper.PeriodicCAlphaDirectionalDerivative
import GlobalEmbedding.Paper.PeriodicCAlphaSpace
import GlobalEmbedding.Paper.PeriodicCAlphaSupremumBounds

/-!
# Actual periodic Hölder norm bound for directional differentiation

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-directional-derivative-norm`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Actual differentiation in direction v loses one derivative with norm bound ‖v‖.

Proof: fixed-direction tensor contraction bounds each target jet supremum by ‖v‖ times
the next source jet supremum, and the target Holder seminorm by ‖v‖ times the source one.
The sum of source jets of orders 1 through k+1 is bounded by the full source sum because
the missing order-zero supremum is nonnegative. Source: `lem:balanced`, differentiation. -/
theorem periodicCAlphaDirectionalDerivative_norm {a N k : ℕ} {α : ℝ}
    (v : EuclideanSpace ℝ (Fin a)) (f : PeriodicCAlphaFunction a N (k + 1) α) :
    ‖periodicCAlphaDirectionalDerivative v f‖ ≤ ‖v‖ * ‖f‖ := by
  let D {m : ℕ} (u : PeriodicCAlphaFunction a N m α) (j : ℕ) :=
    sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j u.toFun x‖}
  let H {m : ℕ} (u : PeriodicCAlphaFunction a N m α) :=
    sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
      let d := dist
        (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
      0 < d ∧ r = ‖iteratedFDeriv ℝ m u.toFun x - iteratedFDeriv ℝ m u.toFun y‖ / d ^ α}
  have hD (j : ℕ) : 0 ≤ D f j := by
    apply Real.sSup_nonneg
    rintro r ⟨x, hx, rfl⟩
    exact norm_nonneg _
  have hH : 0 ≤ H f := by
    apply Real.sSup_nonneg
    rintro r ⟨x, y, hd, rfl⟩
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg hd.le _)
  have hderiv (j : ℕ) (hj : j ≤ k) :
      D (periodicCAlphaDirectionalDerivative v f) j ≤ ‖v‖ * D f (j + 1) := by
    apply Real.sSup_le _ (mul_nonneg (norm_nonneg _) (hD _))
    rintro r ⟨x, hx, rfl⟩
    have hbound := (directional_derivative_iterated_bound j f.toFun
      (f.contDiff.of_le (by exact_mod_cast Nat.add_le_add_right hj 1)) v x x).1
    exact hbound.trans (mul_le_mul_of_nonneg_left
      (le_csSup ((periodicCAlpha_supremum_bounds f).1 (j + 1)
        (Nat.add_le_add_right hj 1)) ⟨x, hx, rfl⟩) (norm_nonneg _))
  have hholder : H (periodicCAlphaDirectionalDerivative v f) ≤ ‖v‖ * H f := by
    apply Real.sSup_le _ (mul_nonneg (norm_nonneg _) hH)
    rintro r ⟨x, y, hd, rfl⟩
    have hbound := (directional_derivative_iterated_bound k f.toFun f.contDiff v x y).2
    calc
      _ ≤ (‖v‖ * ‖iteratedFDeriv ℝ (k + 1) f.toFun x -
          iteratedFDeriv ℝ (k + 1) f.toFun y‖) / _ :=
        div_le_div_of_nonneg_right hbound (Real.rpow_nonneg hd.le _)
      _ = ‖v‖ * (‖iteratedFDeriv ℝ (k + 1) f.toFun x -
          iteratedFDeriv ℝ (k + 1) f.toFun y‖ / _) := mul_div_assoc _ _ _
      _ ≤ ‖v‖ * H f := mul_le_mul_of_nonneg_left
        (le_csSup (periodicCAlpha_supremum_bounds f).2 ⟨x, y, hd, rfl⟩) (norm_nonneg _)
  have hsum : (∑ j ∈ Finset.range (k + 1), D f (j + 1)) ≤
      ∑ j ∈ Finset.range (k + 1 + 1), D f j := by
    conv_rhs => rw [Finset.sum_range_succ']
    exact le_add_of_nonneg_right (hD 0)
  change (∑ j ∈ Finset.range (k + 1), D (periodicCAlphaDirectionalDerivative v f) j) +
    H (periodicCAlphaDirectionalDerivative v f) ≤
      ‖v‖ * ((∑ j ∈ Finset.range (k + 1 + 1), D f j) + H f)
  calc
    _ ≤ (∑ j ∈ Finset.range (k + 1), ‖v‖ * D f (j + 1)) + ‖v‖ * H f :=
      add_le_add (Finset.sum_le_sum (fun j hj ↦ hderiv j
        (Nat.le_of_lt_succ (Finset.mem_range.mp hj)))) hholder
    _ = ‖v‖ * ((∑ j ∈ Finset.range (k + 1), D f (j + 1)) + H f) := by
      rw [mul_add, Finset.mul_sum]
    _ ≤ _ := mul_le_mul_of_nonneg_left (add_le_add hsum le_rfl) (norm_nonneg _)

#print axioms periodicCAlphaDirectionalDerivative_norm

end GlobalEmbedding.Paper
