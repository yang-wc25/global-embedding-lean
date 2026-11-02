import GlobalEmbedding.Paper.PeriodicCAlphaValueBound
import GlobalEmbedding.Paper.PeriodicCAlphaNormNonnegative
import Mathlib.Analysis.Calculus.ContDiff.Basic

/-!
# Definiteness of the periodic Hölder norm formula

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-norm-definite`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- The actual periodic Hölder formula vanishes exactly when the underlying lift is zero.

Proof: the value bound implies every value has norm zero if the formula vanishes. Conversely,
all derivatives and top-order differences of the zero function vanish. Their supremum sets
contain only zero, or are empty for the Hölder part, and hence all supremum terms vanish.
Source: `lem:balanced`, usual periodic Hölder norm expansion. -/
theorem periodicCAlphaNorm_eq_zero_iff {a N k : ℕ} {α : ℝ}
    (f : PeriodicCAlphaFunction a N k α) :
    periodicCAlphaNorm f = 0 ↔ f.toFun = 0 := by
  constructor
  · intro h
    funext x
    apply norm_eq_zero.mp
    exact le_antisymm ((periodicCAlpha_value_bound f x).trans h.le) (norm_nonneg _)
  · intro h
    apply le_antisymm _ (periodicCAlphaNorm_nonnegative f)
    unfold periodicCAlphaNorm
    apply add_nonpos
    · apply Finset.sum_nonpos
      intro j hj
      apply Real.sSup_le _ (le_refl 0)
      rintro r ⟨x, hx, rfl⟩
      simp [h]
    · apply Real.sSup_le _ (le_refl 0)
      rintro r ⟨x, y, hd, rfl⟩
      simp [h]

#print axioms periodicCAlphaNorm_eq_zero_iff

end GlobalEmbedding.Paper
