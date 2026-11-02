import Mathlib.LinearAlgebra.Lagrange
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith

/-!
# Explicit coefficients for a finite-moment smoothing kernel

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`thm:repair`, lines 700–702; the proposed dependency `repair-moment-kernel`,
step 2. This file proves the scalar interpolation step, including an explicit
choice of distinct positive dilation factors. It does not assert that the
analytic smoothing kernel or the full repair theorem has been constructed.

For distinct nodes `lambda i`, evaluate the native Lagrange basis at zero.
The interpolation identity for `X ^ k` then gives mass one for `k = 0` and
vanishing moments for `1 ≤ k ≤ r`. Thus no additional inversion or
Vandermonde hypothesis is needed. The coefficients are allowed to be signed.
The construction includes `r = 0`.

This is an isolated, unaccepted candidate; it does not alter the shared
project, its targets, or its coordination records.
-/

open scoped BigOperators

namespace GlobalEmbedding.Offline

/-- The coefficient of a dilation is the value at zero of its Lagrange basis
polynomial. This is actual data, defined independently of the moment proofs. -/
noncomputable def momentCoefficient {r : ℕ} (lambda : Fin (r + 1) → ℝ)
    (i : Fin (r + 1)) : ℝ :=
  (Lagrange.basis Finset.univ lambda i).eval 0

/-- Evaluation at zero is the stated finite linear combination of evaluations
at the nodes, for every polynomial of degree at most `r`.

Proof: apply Mathlib's exact polynomial interpolation identity, evaluate it
at zero, and commute the scalar factors in the finite sum. -/
theorem momentCoefficient_eval {r : ℕ} (lambda : Fin (r + 1) → ℝ)
    (hlambda : Function.Injective lambda) (p : Polynomial ℝ)
    (hp : p.degree < (r + 1 : ℕ)) :
    (∑ i, momentCoefficient lambda i * p.eval (lambda i)) = p.eval 0 := by
  have hpoly := Lagrange.eq_interpolate
    (s := Finset.univ) (v := lambda) (f := p)
    (fun i _ j _ h => hlambda h) (by simpa using hp)
  have heval := congrArg (Polynomial.eval (0 : ℝ)) hpoly
  simpa [momentCoefficient, Lagrange.interpolate_apply,
    Polynomial.eval_finsetSum, mul_comm] using heval.symm

/-- The explicitly defined interpolation coefficients have mass one and
vanishing scalar moments through order `r`.

Proof: use `momentCoefficient_eval` for `X ^ k`, whose degree is `k`, and
evaluate `0 ^ k`, separating the constant polynomial case. -/
theorem momentCoefficient_power {r : ℕ} (lambda : Fin (r + 1) → ℝ)
    (hlambda : Function.Injective lambda) {k : ℕ} (hk : k ≤ r) :
    (∑ i, momentCoefficient lambda i * lambda i ^ k) =
      if k = 0 then 1 else 0 := by
  have hdegree : (Polynomial.X ^ k : Polynomial ℝ).degree < (r + 1 : ℕ) := by
    simpa only [Polynomial.degree_X_pow, Nat.cast_lt] using Nat.lt_succ_of_le hk
  have h := momentCoefficient_eval lambda hlambda (Polynomial.X ^ k) hdegree
  by_cases hk0 : k = 0
  · simpa [hk0] using h
  · simpa [hk0] using h

/-- In particular, the finite interpolation coefficients sum to one. -/
theorem momentCoefficient_sum {r : ℕ} (lambda : Fin (r + 1) → ℝ)
    (hlambda : Function.Injective lambda) :
    (∑ i, momentCoefficient lambda i) = 1 := by
  simpa using momentCoefficient_power lambda hlambda (Nat.zero_le r)

/-- The dilation factors `(i + 1) / (r + 2)` are fixed by `r`; they are
strictly positive, distinct, and smaller than one. -/
noncomputable def momentDilation (r : ℕ) (i : Fin (r + 1)) : ℝ :=
  ((i.val : ℝ) + 1) / ((r : ℝ) + 2)

/-- Strict positivity of every explicit dilation factor, including `r = 0`. -/
theorem momentDilation_pos (r : ℕ) (i : Fin (r + 1)) :
    0 < momentDilation r i := by
  unfold momentDilation
  positivity

/-- Every explicit dilation shrinks the original support strictly. -/
theorem momentDilation_lt_one (r : ℕ) (i : Fin (r + 1)) :
    momentDilation r i < 1 := by
  have hden : 0 < (r : ℝ) + 2 := by positivity
  have hi : (i.val : ℝ) < (r : ℝ) + 1 := by exact_mod_cast i.isLt
  unfold momentDilation
  apply (div_lt_one hden).2
  linarith

/-- The explicit dilations are pairwise distinct.

Proof: cancel their common nonzero denominator and then cancel the added
one; injectivity of the natural-number cast gives equality of the indices. -/
theorem momentDilation_injective (r : ℕ) :
    Function.Injective (momentDilation r) := by
  intro i j hij
  have hden : (r : ℝ) + 2 ≠ 0 := by positivity
  have hnum : (i.val : ℝ) + 1 = (j.val : ℝ) + 1 :=
    (div_left_inj' hden).mp hij
  apply Fin.ext
  exact_mod_cast (add_right_cancel hnum)

/-- The explicit nodes and the explicitly defined coefficients satisfy all
moment equations. No node selection, matrix inverse, or moment hypothesis
remains as an input. -/
theorem momentDilation_moments (r : ℕ) {k : ℕ} (hk : k ≤ r) :
    (∑ i, momentCoefficient (momentDilation r) i * momentDilation r i ^ k) =
      if k = 0 then 1 else 0 :=
  momentCoefficient_power (momentDilation r) (momentDilation_injective r) hk

/-- The scalar coefficient package needed for the finite-moment kernel:
`r + 1` distinct dilations in `(0,1]` and signed coefficients with every
required moment. The witnesses are the explicit constructions above. -/
theorem exists_positive_moment_coefficients (r : ℕ) :
    ∃ (lambda a : Fin (r + 1) → ℝ),
      Function.Injective lambda ∧
      (∀ i, lambda i ∈ Set.Ioc (0 : ℝ) 1) ∧
      ∀ k ≤ r, (∑ i, a i * lambda i ^ k) = if k = 0 then 1 else 0 := by
  refine ⟨momentDilation r, momentCoefficient (momentDilation r),
    momentDilation_injective r, ?_, ?_⟩
  · intro i
    exact ⟨momentDilation_pos r i, (momentDilation_lt_one r i).le⟩
  · intro k hk
    exact momentDilation_moments r hk

end GlobalEmbedding.Offline
