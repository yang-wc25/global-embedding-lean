import GlobalEmbedding.Paper.PeriodicCAlphaFunction

/-!
# Finite real bounds for the periodic Hölder supremum sets

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-supremum-bounds`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Every supremum set used in the actual periodic Hölder formula is bounded above.

Proof: use the derivative and Hölder boundedness fields of the actual finite-norm carrier.
This does not use any convention for the supremum of unbounded real sets.
Source: `lem:balanced`, periodic Hölder ambient-space expansion. -/
theorem periodicCAlpha_supremum_bounds {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) :
    (∀ j ≤ k, BddAbove {r : ℝ | ∃ x : EuclideanSpace ℝ (Fin a),
      (∀ i, x i ∈ Icc (0 : ℝ) 1) ∧ r = ‖iteratedFDeriv ℝ j f.toFun x‖}) ∧
    BddAbove {r : ℝ | ∃ x y : EuclideanSpace ℝ (Fin a),
      let d := dist
        (toLp 2 (fun i : Fin a ↦ (x i : AddCircle (1 : ℝ))))
        (toLp 2 (fun i : Fin a ↦ (y i : AddCircle (1 : ℝ))))
      0 < d ∧ r = ‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ / d ^ α} := by
  constructor
  · intro j hj
    obtain ⟨C, hC⟩ := f.derivative_bounded j hj
    refine ⟨C, ?_⟩
    rintro r ⟨x, hx, rfl⟩
    exact hC x hx
  · obtain ⟨C, hC⟩ := f.holder_bounded
    refine ⟨C, ?_⟩
    rintro r ⟨x, y, hd, rfl⟩
    exact hC x y hd

#print axioms periodicCAlpha_supremum_bounds

end GlobalEmbedding.Paper
