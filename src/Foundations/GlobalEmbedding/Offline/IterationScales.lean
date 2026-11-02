import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.Algebra.InfiniteSum.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Positivity

/-!
# Summable scales for the repair and probe constructions

Source: `literature/parallelizable-stable-plus-one/main.tex`, equations (6.5),
(6.8), and the finite-wait paragraph at lines 772–776; also the probe-tail
estimates at lines 905–925. This file treats the actual scale
`t_j = t₀ ^ ((6/5)^j)`, with real powers. It supplies a geometric majorant,
summability, and explicit total budgets for every positive power of the scale.
These are numerical dependencies, not a proof of the geometric iteration.
-/

open Filter
open scoped Topology

namespace GlobalEmbedding.Offline

/-- The prescribed scale is independent of the finite stage-exit schedule. -/
noncomputable def iterationScale (t : ℝ) (j : ℕ) : ℝ :=
  t ^ ((6 / 5 : ℝ) ^ j)

/-- The first scale is the chosen initial scale. -/
@[simp] theorem iterationScale_zero (t : ℝ) : iterationScale t 0 = t := by
  simp [iterationScale]

/-- The sequence obeys the exact recurrence from the manuscript. -/
theorem iterationScale_succ {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    iterationScale t (j + 1) = iterationScale t j ^ (6 / 5 : ℝ) := by
  rw [iterationScale, pow_succ, Real.rpow_mul ht]
  rfl

/-- All scales are positive for a positive initial scale. -/
theorem iterationScale_pos {t : ℝ} (ht : 0 < t) (j : ℕ) :
    0 < iterationScale t j :=
  Real.rpow_pos_of_pos ht _

/-- Every scale remains below one. -/
theorem iterationScale_lt_one {t : ℝ} (ht : 0 ≤ t) (ht1 : t < 1) (j : ℕ) :
    iterationScale t j < 1 :=
  Real.rpow_lt_one ht ht1 (pow_pos (by norm_num) _)

/-- Bernoulli's inequality in the precise form needed by the paper. -/
theorem iterationScale_exponent_lower (j : ℕ) :
    1 + (j : ℝ) / 5 ≤ (6 / 5 : ℝ) ^ j := by
  convert one_add_mul_le_pow (a := (1 / 5 : ℝ)) (by norm_num) j using 1 <;>
    norm_num [div_eq_mul_inv]

/-- Any positive power of the actual scale is bounded by one geometric series.

Proof: `(6/5)^j ≥ 1+j/5`, and real powers with base in `(0,1)` reverse the
exponent order. Splitting the lower exponent gives the displayed majorant. -/
theorem iterationScale_power_le_geometric {t p : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hp : 0 ≤ p) (j : ℕ) :
    iterationScale t j ^ p ≤ t ^ p * (t ^ (p / 5)) ^ j := by
  have hexp : p * (1 + (j : ℝ) / 5) ≤ p * (6 / 5 : ℝ) ^ j :=
    mul_le_mul_of_nonneg_left (iterationScale_exponent_lower j) hp
  calc
    iterationScale t j ^ p = t ^ (p * (6 / 5 : ℝ) ^ j) := by
      rw [iterationScale, ← Real.rpow_mul ht.le, mul_comm]
    _ ≤ t ^ (p * (1 + (j : ℝ) / 5)) :=
      Real.rpow_le_rpow_of_exponent_ge ht ht1 hexp
    _ = t ^ p * (t ^ (p / 5)) ^ j := by
      rw [show p * (1 + (j : ℝ) / 5) = p + (p / 5) * j by ring,
        Real.rpow_add ht, Real.rpow_mul_natCast ht.le]

/-- Every positive power of the iteration scale is summable. No schedule or
initial higher-derivative bound is required for this numerical fact. -/
theorem summable_iterationScale_power {t p : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    Summable (fun j : ℕ ↦ iterationScale t j ^ p) := by
  have hratio0 : 0 ≤ t ^ (p / 5) := Real.rpow_nonneg ht.le _
  have hratio1 : t ^ (p / 5) < 1 := Real.rpow_lt_one ht.le ht1 (by positivity)
  exact ((summable_geometric_of_lt_one hratio0 hratio1).mul_left (t ^ p)).of_nonneg_of_le
    (fun j ↦ Real.rpow_nonneg (iterationScale_pos ht j).le p)
    (iterationScale_power_le_geometric ht ht1.le hp.le)

/-- An explicit total budget for any positive power of the actual scales. -/
theorem tsum_iterationScale_power_le {t p : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    (∑' j : ℕ, iterationScale t j ^ p) ≤ t ^ p / (1 - t ^ (p / 5)) := by
  have hratio0 : 0 ≤ t ^ (p / 5) := Real.rpow_nonneg ht.le _
  have hratio1 : t ^ (p / 5) < 1 := Real.rpow_lt_one ht.le ht1 (by positivity)
  have hgeom := summable_geometric_of_lt_one hratio0 hratio1
  calc
    (∑' j : ℕ, iterationScale t j ^ p) ≤
        ∑' j : ℕ, t ^ p * (t ^ (p / 5)) ^ j :=
      (summable_iterationScale_power ht ht1 hp).tsum_le_tsum
        (iterationScale_power_le_geometric ht ht1.le hp.le) (hgeom.mul_left _)
    _ = t ^ p / (1 - t ^ (p / 5)) := by
      rw [hgeom.tsum_mul_left, tsum_geometric_of_lt_one hratio0 hratio1]
      rfl

/-- The convenient factor-two budget holds under one explicit ratio condition. -/
theorem tsum_iterationScale_power_le_twice {t p : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hp : 0 < p)
    (hratio : t ^ (p / 5) ≤ 1 / 2) :
    (∑' j : ℕ, iterationScale t j ^ p) ≤ 2 * t ^ p := by
  apply (tsum_iterationScale_power_le ht ht1 hp).trans
  have hden : 0 < 1 - t ^ (p / 5) := by linarith
  apply (div_le_iff₀ hden).2
  have hnonneg : 0 ≤ t ^ p := Real.rpow_nonneg ht.le p
  nlinarith

/-- The actual iteration scales are summable. -/
theorem summable_iterationScale {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Summable (iterationScale t) := by
  simpa using summable_iterationScale_power ht ht1 (show (0 : ℝ) < 1 by norm_num)

/-- Consequently the actual scales tend to zero. -/
theorem tendsto_iterationScale_zero {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (iterationScale t) atTop (𝓝 0) :=
  (summable_iterationScale ht ht1).tendsto_atTop_zero

/-- Every positive power tends to zero, which discharges the actual
finite-wait coefficients `C_m(k) * t_j^(1/5)` after fixing a stage. -/
theorem tendsto_iterationScale_power_zero {t p : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hp : 0 < p) :
    Tendsto (fun j : ℕ ↦ iterationScale t j ^ p) atTop (𝓝 0) :=
  (summable_iterationScale_power ht ht1 hp).tendsto_atTop_zero

/-- Restarting the prescribed scale at a finite time gives exactly the same
tail, without changing the sequence or choosing a subsequence. -/
theorem iterationScale_add {t : ℝ} (ht : 0 ≤ t) (m j : ℕ) :
    iterationScale t (m + j) = iterationScale (iterationScale t m) j := by
  simp only [iterationScale, pow_add, Real.rpow_mul ht]

/-- A tail budget in terms of its actual first scale. This applies to the
repair limit and the exact probe tail beginning at `t₁=t^(6/5)`. -/
theorem tsum_iterationScale_tail_power_le {t p : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hp : 0 < p) (m : ℕ) :
    (∑' j : ℕ, iterationScale t (m + j) ^ p) ≤
      iterationScale t m ^ p / (1 - iterationScale t m ^ (p / 5)) := by
  simp_rw [iterationScale_add ht.le]
  exact tsum_iterationScale_power_le (iterationScale_pos ht m)
    (iterationScale_lt_one ht.le ht1 m) hp

/-- One explicit initial choice controls the geometric ratio. -/
theorem iterationScale_initial_ratio_le_half {t : ℝ}
    (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ)) :
    t ^ ((1 : ℝ) / 5) ≤ 1 / 2 := by
  have h := Real.rpow_le_rpow ht.le htsmall (show 0 ≤ (1 : ℝ) / 5 by norm_num)
  have hhalf : ((1 / 2 : ℝ) ^ (5 : ℕ)) ^ ((1 : ℝ) / 5) = 1 / 2 := by
    rw [← Real.rpow_natCast_mul (by norm_num)]
    norm_num
  exact h.trans_eq hhalf

/-- A concrete admissible starting scale already fits the source's strict
total budget: if `0 < t ≤ (1/2)^5`, then `∑ t_j < 1`.

The bound gives `t^(1/5) ≤ 1/2` by real-power monotonicity; the factor-two
budget is then at most `1/16`, leaving a strict reserve. -/
theorem tsum_iterationScale_lt_one {t : ℝ}
    (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ)) :
    (∑' j : ℕ, iterationScale t j) < 1 := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hbudget := tsum_iterationScale_power_le_twice ht ht1
    (show (0 : ℝ) < 1 by norm_num) (iterationScale_initial_ratio_le_half ht htsmall)
  simp only [Real.rpow_one] at hbudget
  norm_num at htsmall
  linarith

/-- The same one initial threshold controls every power at least one; this
keeps the three probe error budgets on a common scale. -/
theorem tsum_iterationScale_power_le_twice_of_small {t p : ℝ}
    (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ)) (hp : 1 ≤ p) :
    (∑' j : ℕ, iterationScale t j ^ p) ≤ 2 * t ^ p := by
  have ht1 : t < 1 := by norm_num at htsmall ⊢; linarith
  have hratio : t ^ (p / 5) ≤ 1 / 2 :=
    (Real.rpow_le_rpow_of_exponent_ge ht ht1.le (by linarith :
      (1 : ℝ) / 5 ≤ p / 5)).trans (iterationScale_initial_ratio_le_half ht htsmall)
  exact tsum_iterationScale_power_le_twice ht ht1 (by linarith) hratio

/-- The full probe tail begins at the first updated scale, and has the exact
power `(6/5)*p` of the original `t`. -/
theorem tsum_iterationScale_next_power_le {t p : ℝ}
    (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ)) (hp : 1 ≤ p) :
    (∑' j : ℕ, iterationScale (t ^ (6 / 5 : ℝ)) j ^ p) ≤
      2 * t ^ ((6 / 5 : ℝ) * p) := by
  have ht1 : t ≤ 1 := by norm_num at htsmall ⊢; linarith
  have hnext : t ^ (6 / 5 : ℝ) ≤ (1 / 2 : ℝ) ^ (5 : ℕ) :=
    (Real.rpow_le_self_of_le_one ht.le ht1 (by norm_num)).trans htsmall
  simpa only [← Real.rpow_mul ht.le] using
    tsum_iterationScale_power_le_twice_of_small
      (Real.rpow_pos_of_pos ht (6 / 5 : ℝ)) hnext hp

/-- The three exact exponents in equation (8.4) follow from the same scale
sequence and the same initial threshold. This proves the scalar sums, without
assuming that the analytic probe remainder has already been constructed. -/
theorem probe_tail_power_budgets {t : ℝ}
    (ht : 0 < t) (htsmall : t ≤ (1 / 2 : ℝ) ^ (5 : ℕ)) :
    (∑' j : ℕ, iterationScale (t ^ (6 / 5 : ℝ)) j ^ (38 / 5 : ℝ)) ≤
      2 * t ^ (228 / 25 : ℝ) ∧
    (∑' j : ℕ, iterationScale (t ^ (6 / 5 : ℝ)) j ^ (44 / 5 : ℝ)) ≤
      2 * t ^ (264 / 25 : ℝ) ∧
    (∑' j : ℕ, iterationScale (t ^ (6 / 5 : ℝ)) j ^ (10 : ℝ)) ≤
      2 * t ^ (12 : ℝ) := by
  constructor
  · convert tsum_iterationScale_next_power_le ht htsmall
      (show (1 : ℝ) ≤ 38 / 5 by norm_num) using 1
    norm_num
  constructor
  · convert tsum_iterationScale_next_power_le ht htsmall
      (show (1 : ℝ) ≤ 44 / 5 by norm_num) using 1
    norm_num
  · convert tsum_iterationScale_next_power_le ht htsmall
      (show (1 : ℝ) ≤ 10 by norm_num) using 1
    norm_num

#print axioms iterationScale_power_le_geometric
#print axioms summable_iterationScale_power
#print axioms tsum_iterationScale_power_le
#print axioms tsum_iterationScale_lt_one
#print axioms probe_tail_power_budgets

end GlobalEmbedding.Offline
