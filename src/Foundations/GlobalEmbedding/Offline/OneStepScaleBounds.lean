import GlobalEmbedding.Offline.RepairSequenceScales
import GlobalEmbedding.Offline.CoordinateStageSeries
import Mathlib.Tactic.FinCases

/-!
# The actual six normalized powers of a repair step

Source: `thm:repair`, equations (6.5)–(6.8), and `repair-one-step`.
This file proves the exact scalar substitutions and estimates for BOTH
reserves. It does not assume the six exponents as input and does not claim
the geometric finite-increment estimates themselves have been constructed.
-/

open Set Filter GlobalEmbedding.Paper
open scoped Topology ENNReal

namespace GlobalEmbedding.Offline

/-- The six numerator powers, before dividing by the next defect amplitude:
two finite-increment errors, two tensor smoothing tails, two cross tails.
The actual choice `r=q=40(k+1)` is inserted in these expressions. -/
noncomputable def repairErrorNumeratorExponent (k : ℕ) : Fin 6 → ℝ
  | 0 => (k : ℝ) + (40 * ((k : ℝ) + 1)) / 10
  | 1 => 3 * (k : ℝ) - 6 / 5
  | 2 => 2 * (k : ℝ) + (40 * ((k : ℝ) + 1)) / 10
  | 3 => 2 * (k : ℝ) + (40 * ((k : ℝ) + 1)) / 5
  | 4 => (k : ℝ) + (40 * ((k : ℝ) + 1)) / 10
  | 5 => (k : ℝ) + (40 * ((k : ℝ) + 1)) / 5

/-- The exact six displayed powers in equation (6.7), in source order. -/
noncomputable def repairErrorExponent (k : ℕ) : Fin 6 → ℝ
  | 0 => (13 * (k : ℝ) + 8) / 5
  | 1 => (3 * (k : ℝ) - 18) / 5
  | 2 => (18 * (k : ℝ) + 8) / 5
  | 3 => (38 * (k : ℝ) + 28) / 5
  | 4 => (13 * (k : ℝ) + 8) / 5
  | 5 => (33 * (k : ℝ) + 28) / 5

/-- Dividing by the smaller reserve subtracts exactly `12(k+1)/5`. -/
theorem repairErrorExponent_substitution (k : ℕ) (i : Fin 6) :
    repairErrorNumeratorExponent k i - (12 / 5 : ℝ) * ((k : ℝ) + 1) =
      repairErrorExponent k i := by
  fin_cases i <;> simp only [repairErrorNumeratorExponent, repairErrorExponent] <;> ring

/-- All six exponents have a uniform positive lower bound at every stage.
The sharp minimum over `k≥10` and the six slots is `12/5`. -/
theorem repairErrorExponent_ge (k : ℕ) (hk : 10 ≤ k) (i : Fin 6) :
    (12 / 5 : ℝ) ≤ repairErrorExponent k i := by
  have hk' : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  fin_cases i <;> simp only [repairErrorExponent] <;> linarith

/-- The square of either actual reserve is its stated real power of `t`. -/
theorem repair_reserve_square {t : ℝ} (ht : 0 < t) (s : ℕ) :
    ((t ^ (6 / 5 : ℝ)) ^ s) ^ 2 = t ^ ((12 / 5 : ℝ) * (s : ℝ)) := by
  rw [← pow_mul, ← Real.rpow_natCast (t ^ (6 / 5 : ℝ)) (s * 2),
    ← Real.rpow_mul ht.le]
  congr 1
  push_cast
  ring

/-- Exact actual normalization for the smaller reserve, before any estimate. -/
theorem normalized_repair_error_power {t : ℝ} (ht : 0 < t) (k : ℕ) (i : Fin 6) :
    t ^ repairErrorNumeratorExponent k i / ((t ^ (6 / 5 : ℝ)) ^ (k + 1)) ^ 2 =
      t ^ repairErrorExponent k i := by
  rw [repair_reserve_square ht, ← Real.rpow_sub ht]
  congr 1
  simpa only [Nat.cast_add, Nat.cast_one] using repairErrorExponent_substitution k i

/-- A larger actual reserve only improves the normalized error bound. The
result includes `s=k` and `s=k+1`; no positivity of a denominator is omitted. -/
theorem normalized_repair_error_le
    {t C : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C)
    (k s : ℕ) (hk : 10 ≤ k) (hs : s ≤ k + 1) (i : Fin 6) :
    C * t ^ repairErrorNumeratorExponent k i / ((t ^ (6 / 5 : ℝ)) ^ s) ^ 2 ≤
      C * t ^ (1 / 5 : ℝ) := by
  have hτ : 0 < t ^ (6 / 5 : ℝ) := Real.rpow_pos_of_pos ht _
  have hτ1 : t ^ (6 / 5 : ℝ) ≤ 1 := Real.rpow_le_one ht.le ht1 (by norm_num)
  have hreserve : ((t ^ (6 / 5 : ℝ)) ^ (k + 1)) ^ 2 ≤
      ((t ^ (6 / 5 : ℝ)) ^ s) ^ 2 := by
    exact pow_le_pow_left₀ (pow_nonneg hτ.le _)
      (pow_le_pow_of_le_one hτ.le hτ1 hs) 2
  calc
    C * t ^ repairErrorNumeratorExponent k i / ((t ^ (6 / 5 : ℝ)) ^ s) ^ 2 ≤
        C * t ^ repairErrorNumeratorExponent k i / ((t ^ (6 / 5 : ℝ)) ^ (k + 1)) ^ 2 :=
      div_le_div_of_nonneg_left (mul_nonneg hC (Real.rpow_nonneg ht.le _))
        (pow_pos (pow_pos hτ _) _) hreserve
    _ = C * t ^ repairErrorExponent k i := by
      rw [mul_div_assoc, normalized_repair_error_power ht]
    _ ≤ C * t ^ (1 / 5 : ℝ) :=
      mul_le_mul_of_nonneg_left (Real.rpow_le_rpow_of_exponent_ge ht ht1
        ((show (1 / 5 : ℝ) ≤ 12 / 5 by norm_num).trans (repairErrorExponent_ge k hk i))) hC

/-- The six actual nonnegative error bounds combine into the factor used by
the finite-wait recurrence. The geometric norm estimates remain the explicit
input; only their scalar normalization and summation are discharged here. -/
theorem six_repair_errors_le
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k s : ℕ) (hk : 10 ≤ k) (hs : s ≤ k + 1)
    (error C : Fin 6 → ℝ) (hC : ∀ i, 0 ≤ C i)
    (herror : ∀ i, error i ≤ C i * t ^ repairErrorNumeratorExponent k i /
      ((t ^ (6 / 5 : ℝ)) ^ s) ^ 2) :
    (∑ i, error i) ≤ (∑ i, C i) * t ^ (1 / 5 : ℝ) := by
  calc
    (∑ i, error i) ≤ ∑ i, C i * t ^ (1 / 5 : ℝ) :=
      Finset.sum_le_sum fun i _ ↦ (herror i).trans
        (normalized_repair_error_le ht ht1 (hC i) k s hk hs i)
    _ = _ := (Finset.sum_mul _ _ _).symm

/-- Scale ordering needed by the finite increment, proved from the actual
choices at stage `k≥10`. It applies to both reserve alternatives. -/
theorem repair_step_scale_order {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (k : ℕ) (hk : 10 ≤ k) :
    0 < t ^ k ∧ t ^ k ≤ t ^ (6 / 5 : ℝ) ∧
      t ^ (6 / 5 : ℝ) ≤ t ^ (11 / 10 : ℝ) ∧ t ^ (11 / 10 : ℝ) ≤ t := by
  have hk' : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  refine ⟨pow_pos ht k, ?_, ?_, ?_⟩
  · rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by linarith)
  · exact Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)
  · exact Real.rpow_le_self_of_le_one ht.le ht1 (by norm_num)

/-- The inherited derivative weight ratio is exactly the small factor in
equation (6.8); the smoothing ratio is exactly the factor used in (6.4). -/
theorem repair_step_scale_ratios {t : ℝ} (ht : 0 < t) :
    t ^ (6 / 5 : ℝ) / t = t ^ (1 / 5 : ℝ) ∧
    t ^ (11 / 10 : ℝ) / t = t ^ (1 / 10 : ℝ) ∧
    t ^ (6 / 5 : ℝ) / t ^ (11 / 10 : ℝ) = t ^ (1 / 10 : ℝ) := by
  constructor
  · rw [← Real.rpow_sub_one ht.ne']
    congr 1
    norm_num
  constructor
  · rw [← Real.rpow_sub_one ht.ne']
    congr 1
    norm_num
  · rw [← Real.rpow_sub ht]
    congr 1
    norm_num

/-- The literal six numerator expressions, before replacing products by
single powers. This retains `delta`, `tau`, `ell`, and `r=q=40(k+1)` exactly
as they occur in the finite-error, smoothing, and cross estimates. -/
noncomputable def repairErrorNumerator (t : ℝ) (k : ℕ) : Fin 6 → ℝ
  | 0 => t ^ k * (t ^ (6 / 5 : ℝ) / t ^ (11 / 10 : ℝ)) ^ (40 * (k + 1))
  | 1 => (t ^ k) ^ 3 / t ^ (6 / 5 : ℝ)
  | 2 => (t ^ k) ^ 2 * (t ^ (11 / 10 : ℝ) / t) ^ (40 * (k + 1))
  | 3 => (t ^ k) ^ 2 * (t ^ (6 / 5 : ℝ) / t) ^ (40 * (k + 1))
  | 4 => t ^ k * (t ^ (11 / 10 : ℝ) / t) ^ (40 * (k + 1))
  | 5 => t ^ k * (t ^ (6 / 5 : ℝ) / t) ^ (40 * (k + 1))

/-- The literal products and quotients give exactly the six numerator powers;
the source substitution is proved before normalizing by either reserve. -/
theorem repairErrorNumerator_eq_rpow {t : ℝ} (ht : 0 < t) (k : ℕ) (i : Fin 6) :
    repairErrorNumerator t k i = t ^ repairErrorNumeratorExponent k i := by
  have hpow (a : ℝ) (j : ℕ) : (t ^ a) ^ j = t ^ (a * (j : ℝ)) := by
    rw [Real.rpow_mul ht.le, Real.rpow_natCast]
  have hkpow : t ^ k = t ^ (k : ℝ) := (Real.rpow_natCast t k).symm
  have hratio := repair_step_scale_ratios ht
  fin_cases i <;> simp only [repairErrorNumerator, repairErrorNumeratorExponent,
    hratio.1, hratio.2.1, hratio.2.2, hkpow, hpow, ← Real.rpow_add ht, ← Real.rpow_sub ht]
  all_goals (congr 1; push_cast; ring)

/-- The six expressions in the actual source become the exact six exponents
in equation (6.7), using the smaller of the two allowed reserves. -/
theorem literal_normalized_repair_error {t : ℝ} (ht : 0 < t) (k : ℕ) (i : Fin 6) :
    repairErrorNumerator t k i / ((t ^ (6 / 5 : ℝ)) ^ (k + 1)) ^ 2 =
      t ^ repairErrorExponent k i := by
  rw [repairErrorNumerator_eq_rpow ht]
  exact normalized_repair_error_power ht k i

/-- The actual increment exponent at the growing observation order `⌊k/2⌋`
is strictly greater than one, with no parity assumption on the stage. -/
theorem repair_displacement_exponent_gt_one (k : ℕ) (hk : 10 ≤ k) :
    1 < (k : ℝ) + (6 / 5 : ℝ) * (1 - ((k / 2 : ℕ) : ℝ)) := by
  have hk' : (10 : ℝ) ≤ (k : ℝ) := by exact_mod_cast hk
  have hhalf : 2 * ((k / 2 : ℕ) : ℝ) ≤ (k : ℝ) := by
    exact_mod_cast (show 2 * (k / 2) ≤ k by omega)
  linarith

/-- A fixed stage's finite increment constant is absorbed into the prescribed
summable displacement budget after a finite wait. No uniform bound over
future stage constants is needed. -/
theorem eventually_repair_displacement_power_budget
    {t ρ : ℝ} (ht : 0 < t) (ht1 : t < 1) (hρ : 0 < ρ)
    (k : ℕ) (hk : 10 ≤ k) (C : ℝ) :
    ∀ᶠ j in atTop,
      C * iterationScale t j ^ ((k : ℝ) + (6 / 5 : ℝ) * (1 - ((k / 2 : ℕ) : ℝ))) <
        (ρ / 8) * iterationScale t j := by
  let a : ℝ := (k : ℝ) + (6 / 5 : ℝ) * (1 - ((k / 2 : ℕ) : ℝ))
  have ha : 0 < a - 1 := sub_pos.mpr (repair_displacement_exponent_gt_one k hk)
  filter_upwards [eventually_repair_positive_power_small ht ht1 ha
    (by positivity : 0 < ρ / 8) C] with j hj
  have hs := iterationScale_pos ht j
  change C * iterationScale t j ^ a < (ρ / 8) * iterationScale t j
  calc
    C * iterationScale t j ^ a = (C * iterationScale t j ^ (a - 1)) * iterationScale t j := by
      rw [Real.rpow_sub_one hs.ne']
      field_simp
    _ < (ρ / 8) * iterationScale t j := mul_lt_mul_of_pos_right hj hs

/-- The preceding scalar absorption supplies the actual original coordinate
norm budget for any increments with the finite solver's displayed estimate. -/
theorem eventually_paper_increment_displacement_budget
    {n q : ℕ} (u : ℕ → (Fin n → ℝ) → Fin q → ℝ) (O S : Set (Fin n → ℝ))
    {t ρ : ℝ} (ht : 0 < t) (ht1 : t < 1) (hρ : 0 < ρ)
    (k : ℕ) (hk : 10 ≤ k) (C : ℝ)
    (hbound : ∀ j, paperCoordinateCj (k / 2) (u j) O S ≤
      ENNReal.ofReal (C * iterationScale t j ^
        ((k : ℝ) + (6 / 5 : ℝ) * (1 - ((k / 2 : ℕ) : ℝ))))) :
    ∀ᶠ j in atTop, paperCoordinateCj (k / 2) (u j) O S <
      ENNReal.ofReal ((ρ / 8) * iterationScale t j) := by
  filter_upwards [eventually_repair_displacement_power_budget ht ht1 hρ k hk C] with j hj
  exact (hbound j).trans_lt ((ENNReal.ofReal_lt_ofReal_iff
    (mul_pos (by positivity) (iterationScale_pos ht j))).2 hj)

#print axioms repairErrorExponent_substitution
#print axioms repairErrorExponent_ge
#print axioms repair_reserve_square
#print axioms normalized_repair_error_power
#print axioms normalized_repair_error_le
#print axioms six_repair_errors_le
#print axioms repair_step_scale_order
#print axioms repair_step_scale_ratios
#print axioms repairErrorNumerator_eq_rpow
#print axioms literal_normalized_repair_error
#print axioms repair_displacement_exponent_gt_one
#print axioms eventually_repair_displacement_power_budget
#print axioms eventually_paper_increment_displacement_budget

end GlobalEmbedding.Offline
