import GlobalEmbedding.Paper.PeriodicCAlphaRestrictOrder

/-!
# Full actual norm bound for lowering Hölder regularity

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 382–418.
DAG node: `balanced-holder-restrict-order-norm`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The original lower Hölder norm of the unchanged lift is bounded by its original higher norm.

Every lower derivative supremum is bounded by the original full norm. The actual all-jet
quotient bound controls the lower top seminorm. Take the real suprema, including the empty
quotient set, then add the j+1 derivative bounds. Source: bounded regularity inclusions used
in the vertical translation derivative argument of `lem:balanced`. -/
theorem periodicCAlphaRestrictOrder_norm {a N k : ℕ} {α : ℝ}
    (j : ℕ) (hj : j ≤ k) (hα : α ≤ 1) (f : PeriodicCAlphaFunction a N k α) (D : ℝ)
    (hdiam : ∀ x y : EuclideanSpace ℝ (Fin a),
      dist (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ)))) ≤ D) :
    ‖periodicCAlphaRestrictOrder j hj hα f‖ ≤
      ((j + 1 : ℕ) + (1 + D ^ (1 - α))) * ‖f‖ := by
  have hD0 : 0 ≤ D := by simpa only [dist_self] using hdiam 0 0
  have hC : 0 ≤ 1 + D ^ (1 - α) := by positivity
  have hjet (i : ℕ) (hi : i ≤ j) :
      sSup {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
        (∀ l, x l ∈ Icc (0 : ℝ) 1) ∧
        r = ‖iteratedFDeriv ℝ i (periodicCAlphaRestrictOrder j hj hα f).toFun x‖} ≤ ‖f‖ := by
    apply Real.sSup_le _ (norm_nonneg f)
    rintro r ⟨x, hx, rfl⟩
    exact periodicCAlpha_global_jet_bound f i (hi.trans hj) x
  have hholder :
      sSup {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
        let d := dist
          (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
          (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
        0 < d ∧ r =
          ‖iteratedFDeriv ℝ j (periodicCAlphaRestrictOrder j hj hα f).toFun x -
            iteratedFDeriv ℝ j (periodicCAlphaRestrictOrder j hj hα f).toFun y‖ / d ^ α} ≤
        (1 + D ^ (1 - α)) * ‖f‖ := by
    apply Real.sSup_le _ (mul_nonneg hC (norm_nonneg f))
    rintro r ⟨x, y, hd, rfl⟩
    exact periodicCAlpha_all_jet_holder_bound f hα D hdiam j hj x y hd
  change periodicCAlphaNorm (periodicCAlphaRestrictOrder j hj hα f) ≤ _
  unfold periodicCAlphaNorm
  calc
    _ ≤ (∑ i ∈ Finset.range (j + 1), ‖f‖) + (1 + D ^ (1 - α)) * ‖f‖ :=
      add_le_add (Finset.sum_le_sum (fun i hi ↦ hjet i
        (Nat.le_of_lt_succ (Finset.mem_range.mp hi)))) hholder
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
      ring

#print axioms periodicCAlphaRestrictOrder_norm

end GlobalEmbedding.Paper
