import GlobalEmbedding.Offline.FiniteWait
import GlobalEmbedding.Offline.IterationScales

/-!
# Actual repair scales in finite waits and the defect limit

Source: `thm:repair`, equations (6.5), (6.8), and the finite-wait and limit
paragraphs at main.tex lines 772–778. The stage is allowed to vary without
any assumed uniform bound on its stage-dependent constants. Fixed-stage
waiting and the arbitrary-stage defect decay are kept separate, as required
by the actual proof.
-/

open Filter
open scoped Topology

namespace GlobalEmbedding.Offline

/-- The finite-wait theorem remains valid when its recurrence starts only
after a finite entrance time. Earlier high-order norms are unrestricted. -/
theorem finite_wait_eventually_le_of_eventual_recurrence
    {x c : ℕ → ℝ} {A : ℝ} (hA : 0 ≤ A)
    (hc_nonneg : ∀ n, 0 ≤ c n) (hc : Tendsto c atTop (𝓝 0))
    (hstep : ∀ᶠ n in atTop, x (n + 1) ≤ A + c n * (1 + x n))
    {η : ℝ} (hη : 0 < η) :
    ∀ᶠ n in atTop, x n ≤ A + η := by
  obtain ⟨N, hN⟩ := eventually_atTop.1 hstep
  have hshift := finite_wait_eventually_le (x := fun n ↦ x (n + N))
    (c := fun n ↦ c (n + N)) hA (fun n ↦ hc_nonneg (n + N))
    (hc.comp (tendsto_add_atTop_nat N))
    (fun n ↦ by simpa only [Nat.add_right_comm] using hN (n + N) (by omega)) hη
  obtain ⟨J, hJ⟩ := eventually_atTop.1 hshift
  refine eventually_atTop.2 ⟨J + N, ?_⟩
  intro n hn
  have hnN : N ≤ n := by omega
  have h := hJ (n - N) (by omega)
  simpa only [Nat.sub_add_cancel hnN] using h

/-- At each FIXED stage, the actual coefficient `C*t_j^(1/5)` tends to zero.
The constant is arbitrary and may depend on that stage and observation order;
no bound uniform over all future stages is asserted or used. -/
theorem tendsto_repair_fixed_stage_coefficient_zero
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1) (C : ℝ) :
    Tendsto (fun j ↦ C * iterationScale t j ^ (1 / 5 : ℝ)) atTop (𝓝 0) := by
  simpa only [mul_zero] using
    (tendsto_iterationScale_power_zero ht ht1 (show (0 : ℝ) < 1 / 5 by norm_num)).const_mul C

/-- The source's actual fixed-stage recurrence reaches the next `B/2`
threshold, even if it only becomes available after a finite entrance time.
The argument needs no smallness of the initial higher-order norm. -/
theorem repair_fixed_stage_finite_wait
    {x : ℕ → ℝ} {t C B : ℝ}
    (ht : 0 < t) (ht1 : t < 1) (hC : 0 ≤ C) (hB : 0 < B)
    (hstep : ∀ᶠ j in atTop,
      x (j + 1) ≤ B / 4 + C * iterationScale t j ^ (1 / 5 : ℝ) * (1 + x j)) :
    ∀ᶠ j in atTop, x j < B / 2 := by
  have h := finite_wait_eventually_le_of_eventual_recurrence
    (A := B / 4) (by linarith)
    (fun j ↦ mul_nonneg hC (Real.rpow_nonneg (iterationScale_pos ht j).le _))
    (tendsto_repair_fixed_stage_coefficient_zero ht ht1 C) hstep
    (η := B / 8) (by linarith)
  filter_upwards [h] with j hj
  linarith

/-- Every prescribed finite collection of next-stage norms has one finite
waiting threshold at a fixed stage, using the actual common scale sequence. -/
theorem repair_fixed_stage_common_wait
    {ι : Type*} [Finite ι] (x : ι → ℕ → ℝ) (C : ι → ℝ)
    {t B : ℝ} (ht : 0 < t) (ht1 : t < 1) (hC : ∀ i, 0 ≤ C i) (hB : 0 < B)
    (hstep : ∀ i, ∀ᶠ j in atTop,
      x i (j + 1) ≤ B / 4 + C i * iterationScale t j ^ (1 / 5 : ℝ) * (1 + x i j)) :
    ∃ J : ℕ, ∀ j ≥ J, ∀ i, x i j < B / 2 := by
  apply eventually_atTop.1
  exact eventually_all.2 fun i ↦
    repair_fixed_stage_finite_wait ht ht1 (hC i) hB (hstep i)

/-- At every time the actual defect amplitude is bounded by `t_j^10`,
independently of how long a block lasts or when its stage exits. -/
theorem repair_defect_scale_le_tenth_power
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (stage : ℕ → ℕ) (hstage : ∀ j, 10 ≤ stage j) (j : ℕ) :
    iterationScale t j ^ stage j ≤ iterationScale t j ^ (10 : ℕ) :=
  pow_le_pow_of_le_one (iterationScale_pos ht j).le
    (iterationScale_lt_one ht.le ht1 j).le (hstage j)

/-- The actual varying-stage defect amplitudes are even summable. There is
no hidden assumption that the stage is fixed, monotone, or bounded above. -/
theorem summable_repair_defect_scale
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (stage : ℕ → ℕ) (hstage : ∀ j, 10 ≤ stage j) :
    Summable (fun j ↦ iterationScale t j ^ stage j) := by
  have hten : Summable (fun j ↦ iterationScale t j ^ (10 : ℕ)) := by
    simpa only [Real.rpow_ofNat] using
      summable_iterationScale_power ht ht1 (show (0 : ℝ) < 10 by norm_num)
  exact hten.of_nonneg_of_le
    (fun j ↦ pow_nonneg (iterationScale_pos ht j).le _)
    (repair_defect_scale_le_tenth_power ht ht1 stage hstage)

/-- This supplies the vanishing-scale hypothesis in the actual induced-metric
limit theorem with exactly `δ_j = t_j^(k_j)`, as in the manuscript. -/
theorem tendsto_repair_defect_scale_zero
    {t : ℝ} (ht : 0 < t) (ht1 : t < 1)
    (stage : ℕ → ℕ) (hstage : ∀ j, 10 ≤ stage j) :
    Tendsto (fun j ↦ iterationScale t j ^ stage j) atTop (𝓝 0) :=
  (summable_repair_defect_scale ht ht1 stage hstage).tendsto_atTop_zero

/-- Every fixed positive-power smallness test becomes true after a finite
wait. This is used together with the finite list of norm entrance tests. -/
theorem eventually_repair_positive_power_small
    {t p ε : ℝ} (ht : 0 < t) (ht1 : t < 1) (hp : 0 < p) (hε : 0 < ε) (C : ℝ) :
    ∀ᶠ j in atTop, C * iterationScale t j ^ p < ε := by
  have hlimit : Tendsto (fun j ↦ C * iterationScale t j ^ p) atTop (𝓝 0) := by
    simpa only [mul_zero] using (tendsto_iterationScale_power_zero ht ht1 hp).const_mul C
  exact hlimit.eventually (eventually_lt_nhds hε)

#print axioms finite_wait_eventually_le_of_eventual_recurrence
#print axioms tendsto_repair_fixed_stage_coefficient_zero
#print axioms repair_fixed_stage_finite_wait
#print axioms repair_fixed_stage_common_wait
#print axioms repair_defect_scale_le_tenth_power
#print axioms summable_repair_defect_scale
#print axioms tendsto_repair_defect_scale_zero
#print axioms eventually_repair_positive_power_small

end GlobalEmbedding.Offline
