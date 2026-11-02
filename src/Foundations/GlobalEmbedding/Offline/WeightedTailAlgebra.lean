import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic
import Mathlib.Tactic

/-!
# Finite low/high weighted tail summation

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 704–719,
the final scalar step in equation (6.4). Input and output profiles are
the cumulative Cj quantities in the application. This arithmetic lemma
does not assume a weighted tail estimate; it derives it from the two
individual-order estimates and the displayed weighted input bound.
-/

open scoped BigOperators

namespace GlobalEmbedding.Offline

/-- Summing genuine low- and high-order estimates gives the two-term
weighted tail. Only tau≤ell≤t is used here; ell≤1 is used earlier when
passing from exact jets to cumulative Cj norms. -/
theorem weighted_low_high_tail (m r : ℕ) (I A : ℕ → ℝ)
    (hI : ∀ a, 0 ≤ I a) (L H : ℝ) (hL : 0 ≤ L) (hH : 0 ≤ H)
    {tau ell t : ℝ} (htau : 0 ≤ tau) (htaul : tau ≤ ell) (helt : ell ≤ t)
    (ht : 0 < t) (B : ℝ)
    (hNr : (∑ a ∈ Finset.range (r + 1), t ^ a * I a) ≤ B)
    (hlow : ∀ a ≤ m, a ≤ r → A a ≤ L * ell ^ (r - a) * I r)
    (hhigh : ∀ a ≤ m, A a ≤ H * I a) :
    (∑ a ∈ Finset.range (m + 1), tau ^ a * A a) ≤
      (((m + 1 : ℕ) : ℝ) * L + H) *
        (B * (ell / t) ^ r +
          (∑ a ∈ Finset.range (m + 1), t ^ a * I a) * (tau / t) ^ r) := by
  have hell : 0 ≤ ell := htau.trans htaul
  have hB0 : 0 ≤ B := (Finset.sum_nonneg (fun a _ =>
    mul_nonneg (pow_nonneg ht.le a) (hI a))).trans hNr
  have hIr : t ^ r * I r ≤ B :=
    (Finset.single_le_sum (fun a _ => mul_nonneg (pow_nonneg ht.le a) (hI a))
      (Finset.mem_range.mpr (Nat.lt_succ_self r))).trans hNr
  have hratio : tau / t ≤ 1 := (div_le_one ht).mpr (htaul.trans helt)
  have hratio0 : 0 ≤ tau / t := div_nonneg htau ht.le
  have hlow0 : 0 ≤ L * B * (ell / t) ^ r := by positivity
  have hhigh0 (a : ℕ) : 0 ≤ H * (tau / t) ^ r * (t ^ a * I a) := by
    exact mul_nonneg (mul_nonneg hH (pow_nonneg hratio0 _))
      (mul_nonneg (pow_nonneg ht.le _) (hI a))
  have hterm : ∀ a ∈ Finset.range (m + 1), tau ^ a * A a ≤
      L * B * (ell / t) ^ r + H * (tau / t) ^ r * (t ^ a * I a) := by
    intro a ha
    have ham : a ≤ m := Nat.le_of_lt_succ (Finset.mem_range.mp ha)
    by_cases har : a ≤ r
    · have hp : tau ^ a * ell ^ (r - a) ≤ ell ^ r := by
        calc
          _ ≤ ell ^ a * ell ^ (r - a) :=
            mul_le_mul_of_nonneg_right (pow_le_pow_left₀ htau htaul a) (pow_nonneg hell _)
          _ = ell ^ r := by rw [← pow_add, Nat.add_sub_of_le har]
      have h : tau ^ a * A a ≤ L * B * (ell / t) ^ r := by
        calc
          _ ≤ tau ^ a * (L * ell ^ (r - a) * I r) :=
            mul_le_mul_of_nonneg_left (hlow a ham har) (pow_nonneg htau _)
          _ = (L * I r) * (tau ^ a * ell ^ (r - a)) := by ring
          _ ≤ (L * I r) * ell ^ r := mul_le_mul_of_nonneg_left hp (mul_nonneg hL (hI r))
          _ = L * (t ^ r * I r) * (ell / t) ^ r := by
            rw [div_pow]
            field_simp
          _ ≤ L * B * (ell / t) ^ r :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hIr hL)
              (pow_nonneg (div_nonneg hell ht.le) _)
      exact h.trans (le_add_of_nonneg_right (hhigh0 a))
    · have hpow : (tau / t) ^ a ≤ (tau / t) ^ r :=
        pow_le_pow_of_le_one hratio0 hratio (by omega)
      have h : tau ^ a * A a ≤ H * (tau / t) ^ r * (t ^ a * I a) := by
        calc
          _ ≤ tau ^ a * (H * I a) :=
            mul_le_mul_of_nonneg_left (hhigh a ham) (pow_nonneg htau _)
          _ = H * (tau / t) ^ a * (t ^ a * I a) := by
            rw [div_pow]
            field_simp
          _ ≤ H * (tau / t) ^ r * (t ^ a * I a) :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpow hH)
              (mul_nonneg (pow_nonneg ht.le _) (hI a))
      exact h.trans (le_add_of_nonneg_left hlow0)
  have hsum := Finset.sum_le_sum hterm
  simp only [Finset.sum_add_distrib, Finset.sum_const, Finset.card_range, nsmul_eq_mul,
    ← Finset.mul_sum] at hsum
  let X := B * (ell / t) ^ r
  let Y := (∑ a ∈ Finset.range (m + 1), t ^ a * I a) * (tau / t) ^ r
  have hX : 0 ≤ X := mul_nonneg hB0 (pow_nonneg (div_nonneg hell ht.le) _)
  have hY : 0 ≤ Y := mul_nonneg
    (Finset.sum_nonneg fun a _ => mul_nonneg (pow_nonneg ht.le _) (hI a))
    (pow_nonneg hratio0 _)
  calc
    _ ≤ (((m + 1 : ℕ) : ℝ) * L) * X + H * Y := by
      convert hsum using 1
      dsimp [X, Y]
      ring
    _ ≤ ((((m + 1 : ℕ) : ℝ) * L) + H) * X +
        ((((m + 1 : ℕ) : ℝ) * L) + H) * Y := by
      apply add_le_add
      · exact mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hH) hX
      · exact mul_le_mul_of_nonneg_right
          (le_add_of_nonneg_left (mul_nonneg (Nat.cast_nonneg _) hL)) hY
    _ = _ := by rw [← mul_add]

end GlobalEmbedding.Offline
