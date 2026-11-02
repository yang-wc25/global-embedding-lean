import GlobalEmbedding.Paper.PeriodicCAlphaNorm

/-!
# Nonnegativity of the periodic Hölder norm formula

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-norm-nonnegative`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual periodic Hölder norm formula is nonnegative.

Proof: every derivative value is a norm. Every positive-distance Hölder quotient is
nonnegative. A real supremum of a nonnegative set is nonnegative, including the empty-set
convention zero. Sum these nonnegative real quantities.
Source: `lem:balanced`, usual periodic Hölder norm expansion. -/
theorem periodicCAlphaNorm_nonnegative {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) :
    0 ≤ periodicCAlphaNorm f := by
  unfold periodicCAlphaNorm
  apply add_nonneg
  · apply Finset.sum_nonneg
    intro j hj
    apply Real.sSup_nonneg
    rintro r ⟨x, hx, rfl⟩
    exact norm_nonneg _
  · apply Real.sSup_nonneg
    rintro r ⟨x, y, hd, rfl⟩
    exact div_nonneg (norm_nonneg _) (Real.rpow_nonneg (le_of_lt hd) _)

#print axioms periodicCAlphaNorm_nonnegative

end GlobalEmbedding.Paper
