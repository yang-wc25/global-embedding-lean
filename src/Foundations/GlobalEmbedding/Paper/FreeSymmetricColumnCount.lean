import Mathlib.Data.Sym.Card

/-!
# Count of symmetric second partial columns

A symmetric column is an unordered pair with repetition of indices in `Fin a`, represented by
`Sym2 (Fin a)`. Its actual finite cardinality is the paper's `a * (a + 1) / 2`.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Section `sec:introduction`, line 108.
-/

/-- The number of symmetric second partial columns, counted as the cardinality of `Sym2 (Fin a)`. -/
noncomputable def freeSymmetricColumnCount (a : ℕ) : ℕ := Fintype.card (Sym2 (Fin a))

/-- The symmetric-pair index has `a * (a + 1) / 2` elements, including when `a = 0`. -/
theorem free_symmetric_column_count (a : ℕ) :
    freeSymmetricColumnCount a = a * (a + 1) / 2 := by
  simp [freeSymmetricColumnCount, Sym2.card, Nat.choose_two_right, Nat.mul_comm]

#print axioms free_symmetric_column_count
