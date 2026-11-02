import GlobalEmbedding.Offline.FiniteBlockSchedule

/-!
# Least finite exits, including tests depending on the preceding entrance

Source: `repair-finite-wait-convergence`, the least uniform legal exit in the
proof of `thm:repair`. The schedule is recursively constructed, rather than
assuming an increasing entrance sequence. The next stage's tests may depend
on the preceding entrance time. The actual geometric one-step construction
must still supply their eventual validity; it is not fabricated here.
-/

open Filter
open scoped Topology

namespace GlobalEmbedding.Offline

/-- The least strictly later time satisfying an eventual predicate. -/
noncomputable def leastLegalExit (P : ℕ → Prop) (start : ℕ)
    (hP : ∀ᶠ j in atTop, P j) : ℕ := by
  classical
  exact Nat.find ((hP.and (eventually_gt_atTop start)).exists)

/-- This is an actual finite legal time and genuinely ends a nonempty block. -/
theorem leastLegalExit_spec (P : ℕ → Prop) (start : ℕ)
    (hP : ∀ᶠ j in atTop, P j) :
    P (leastLegalExit P start hP) ∧ start < leastLegalExit P start hP := by
  classical
  exact Nat.find_spec ((hP.and (eventually_gt_atTop start)).exists)

/-- Minimality is proved, not an arbitrary choice among legal exits. -/
theorem leastLegalExit_le (P : ℕ → Prop) (start : ℕ)
    (hP : ∀ᶠ j in atTop, P j) {j : ℕ} (hstart : start < j) (hj : P j) :
    leastLegalExit P start hP ≤ j := by
  classical
  exact Nat.find_min' _ ⟨hj, hstart⟩

/-- A strictly later time before the chosen exit fails the stage tests. -/
theorem not_legal_before_leastLegalExit (P : ℕ → Prop) (start : ℕ)
    (hP : ∀ᶠ j in atTop, P j) {j : ℕ}
    (hstart : start < j) (hj : j < leastLegalExit P start hP) : ¬ P j := by
  intro hlegal
  exact (not_lt_of_ge (leastLegalExit_le P start hP hstart hlegal)) hj

/-- Recursive finite entrances. `P k start j` is the exit test for block `k`,
whose input state was entered at `start`. Eventual validity is required for
each such input; no time-uniform bound on waiting lengths is assumed. -/
noncomputable def leastWaitEntries
    (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j) : ℕ → ℕ
  | 0 => 0
  | k + 1 => leastLegalExit (P k (leastWaitEntries P hP k))
      (leastWaitEntries P hP k) (hP k (leastWaitEntries P hP k))

@[simp]
theorem leastWaitEntries_zero (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j) : leastWaitEntries P hP 0 = 0 := rfl

/-- Each recursive exit satisfies the actual tests with its actual previous
entrance, and the block length is positive. -/
theorem leastWaitEntries_succ_spec (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j) (k : ℕ) :
    P k (leastWaitEntries P hP k) (leastWaitEntries P hP (k + 1)) ∧
      leastWaitEntries P hP k < leastWaitEntries P hP (k + 1) :=
  leastLegalExit_spec _ _ _

/-- No earlier strictly later legal exit is skipped in the recursive schedule. -/
theorem leastWaitEntries_succ_le (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j) (k j : ℕ)
    (hstart : leastWaitEntries P hP k < j)
    (hj : P k (leastWaitEntries P hP k) j) :
    leastWaitEntries P hP (k + 1) ≤ j :=
  leastLegalExit_le _ _ _ hstart hj

/-- Every complete block is finite and the actual entrances strictly increase. -/
theorem leastWaitEntries_strictMono (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j) :
    StrictMono (leastWaitEntries P hP) :=
  strictMono_nat_of_lt_succ fun k ↦ (leastWaitEntries_succ_spec P hP k).2

/-- The recursively constructed stage tends to infinity along every natural
time, not merely the entrance subsequence. -/
theorem leastWait_repairStage_tendsto (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j) :
    Tendsto (repairStage (leastWaitEntries P hP)) atTop atTop :=
  tendsto_repairStage_atTop _ (leastWaitEntries_strictMono P hP)

/-- The resulting full-time stage has exactly the intended block intervals. -/
theorem leastWait_stage_block (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j) (j k : ℕ) :
    repairStage (leastWaitEntries P hP) j = 10 + k ↔
      leastWaitEntries P hP k ≤ j ∧ j < leastWaitEntries P hP (k + 1) := by
  simp only [repairStage, Nat.add_left_cancel_iff]
  exact stageIndex_eq_iff _ (leastWaitEntries_strictMono P hP) rfl j k

/-- Same-stage and exit-stage reserves follow for this constructed schedule,
including every finite wait. The scale advances at each actual time step. -/
theorem leastWait_next_reserve (P : ℕ → ℕ → ℕ → Prop)
    (hP : ∀ k start, ∀ᶠ j in atTop, P k start j)
    {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    iterationScale t (j + 1) ^ repairStage (leastWaitEntries P hP) (j + 1) =
      (iterationScale t j ^ (6 / 5 : ℝ)) ^ repairStage (leastWaitEntries P hP) j ∨
    iterationScale t (j + 1) ^ repairStage (leastWaitEntries P hP) (j + 1) =
      (iterationScale t j ^ (6 / 5 : ℝ)) ^ (repairStage (leastWaitEntries P hP) j + 1) :=
  repairStage_next_reserve _ (leastWaitEntries_strictMono P hP) rfl ht j

/-- A finite collection of true recurrence tests and positive-power tests
has one common eventual tail. This supplies the scheduling predicate from
the source's scalar estimates, including any finite extra probe tests.

Each coefficient may depend on its observation order and current fixed stage;
there is no initial higher-norm smallness condition or future-stage bound. -/
theorem repair_norm_and_power_tests_eventually
    {ι κ : Type*} [Finite ι] [Finite κ]
    (x : ι → ℕ → ℝ) (C : ι → ℝ) (D p ε : κ → ℝ)
    {t B : ℝ} (ht : 0 < t) (ht1 : t < 1) (hC : ∀ i, 0 ≤ C i) (hB : 0 < B)
    (hp : ∀ a, 0 < p a) (hε : ∀ a, 0 < ε a)
    (hstep : ∀ i, ∀ᶠ j in atTop,
      x i (j + 1) ≤ B / 4 + C i * iterationScale t j ^ (1 / 5 : ℝ) * (1 + x i j)) :
    ∀ᶠ j in atTop, (∀ i, x i j < B / 2) ∧
      ∀ a, D a * iterationScale t j ^ p a < ε a := by
  exact (eventually_all.2 fun i ↦
    repair_fixed_stage_finite_wait ht ht1 (hC i) hB (hstep i)).and
    (eventually_all.2 fun a ↦
      eventually_repair_positive_power_small ht ht1 (hp a) (hε a) (D a))

/-- The common scalar tests therefore admit an actual LEAST legal time after
any prescribed entrance. Its minimality is retained for deterministic scheduling. -/
theorem exists_least_repair_norm_and_power_exit
    {ι κ : Type*} [Finite ι] [Finite κ]
    (x : ι → ℕ → ℝ) (C : ι → ℝ) (D p ε : κ → ℝ)
    {t B : ℝ} (ht : 0 < t) (ht1 : t < 1) (hC : ∀ i, 0 ≤ C i) (hB : 0 < B)
    (hp : ∀ a, 0 < p a) (hε : ∀ a, 0 < ε a)
    (hstep : ∀ i, ∀ᶠ j in atTop,
      x i (j + 1) ≤ B / 4 + C i * iterationScale t j ^ (1 / 5 : ℝ) * (1 + x i j))
    (start : ℕ) :
    ∃ J : ℕ, start < J ∧ (∀ i, x i J < B / 2) ∧
      (∀ a, D a * iterationScale t J ^ p a < ε a) ∧
      ∀ j, start < j → (∀ i, x i j < B / 2) →
        (∀ a, D a * iterationScale t j ^ p a < ε a) → J ≤ j := by
  let P : ℕ → Prop := fun j ↦ (∀ i, x i j < B / 2) ∧
    ∀ a, D a * iterationScale t j ^ p a < ε a
  have hP : ∀ᶠ j in atTop, P j :=
    repair_norm_and_power_tests_eventually x C D p ε ht ht1 hC hB hp hε hstep
  have h := leastLegalExit_spec P start hP
  exact ⟨leastLegalExit P start hP, h.2, h.1.1, h.1.2,
    fun j hj hnorm hpower ↦ leastLegalExit_le P start hP hj ⟨hnorm, hpower⟩⟩

#print axioms leastLegalExit_spec
#print axioms leastLegalExit_le
#print axioms not_legal_before_leastLegalExit
#print axioms leastWaitEntries_zero
#print axioms leastWaitEntries_succ_spec
#print axioms leastWaitEntries_succ_le
#print axioms leastWaitEntries_strictMono
#print axioms leastWait_repairStage_tendsto
#print axioms leastWait_stage_block
#print axioms leastWait_next_reserve
#print axioms repair_norm_and_power_tests_eventually
#print axioms exists_least_repair_norm_and_power_exit

end GlobalEmbedding.Offline
