import GlobalEmbedding.Offline.RepairSequenceScales
import Mathlib.Data.Nat.Find

/-!
# The actual time schedule determined by finite stage entrances

Source: `thm:repair`, main.tex lines 772–776. Given increasing finite entrance
times, the stage at every natural time is defined explicitly, rather than
passing to a subsequence. Every block is exactly the interval between its
entrances, the stage tends to infinity, and its next reserve is exactly one
of the two reserves specified in equation (6.5).

This does not manufacture the geometric states or their entrance inequalities.
Those still come from the one-step provider and the proved finite-wait tests.
-/

open Filter
open scoped Topology

namespace GlobalEmbedding.Offline

/-- Index of the last stage whose finite entrance has occurred by time `j`.
The finite search bound `j` is valid because a strictly increasing natural
entrance sequence satisfies `k ≤ entry k`. -/
def stageIndex (entry : ℕ → ℕ) (j : ℕ) : ℕ :=
  Nat.findGreatest (fun k ↦ entry k ≤ j) j

/-- The current stage has already entered, including time zero. -/
theorem stageIndex_entered (entry : ℕ → ℕ) (hzero : entry 0 = 0) (j : ℕ) :
    entry (stageIndex entry j) ≤ j := by
  exact Nat.findGreatest_spec (P := fun k ↦ entry k ≤ j) (m := 0)
    (Nat.zero_le j) (by simpa only [hzero] using Nat.zero_le j)

/-- The next stage has not entered yet. This uses strict increase, and does
not assume a uniform upper bound on the durations of the finite blocks. -/
theorem stageIndex_before_next (entry : ℕ → ℕ) (hentry : StrictMono entry) (j : ℕ) :
    j < entry (stageIndex entry j + 1) := by
  by_contra hnot
  have hnext : entry (stageIndex entry j + 1) ≤ j := Nat.le_of_not_gt hnot
  have hindex : stageIndex entry j + 1 ≤ j := (hentry.id_le _).trans hnext
  exact Nat.findGreatest_is_greatest (Nat.lt_succ_self _) hindex hnext

/-- Every stage's block is exactly the finite interval between its entrances. -/
theorem stageIndex_eq_iff
    (entry : ℕ → ℕ) (hentry : StrictMono entry) (hzero : entry 0 = 0) (j k : ℕ) :
    stageIndex entry j = k ↔ entry k ≤ j ∧ j < entry (k + 1) := by
  constructor
  · intro heq
    simpa only [heq] using
      And.intro (stageIndex_entered entry hzero j) (stageIndex_before_next entry hentry j)
  · rintro ⟨hleft, hright⟩
    have hlower : k ≤ stageIndex entry j :=
      Nat.le_findGreatest ((hentry.id_le k).trans hleft) hleft
    have hupper : stageIndex entry j ≤ k := by
      by_contra hnot
      have hki : k + 1 ≤ stageIndex entry j := by omega
      have h := (hentry.monotone hki).trans (stageIndex_entered entry hzero j)
      omega
    exact le_antisymm hupper hlower

/-- In particular each prescribed finite entrance is genuinely reached. -/
theorem stageIndex_at_entry
    (entry : ℕ → ℕ) (hentry : StrictMono entry) (hzero : entry 0 = 0) (k : ℕ) :
    stageIndex entry (entry k) = k :=
  (stageIndex_eq_iff entry hentry hzero (entry k) k).2
    ⟨le_rfl, hentry (Nat.lt_succ_self k)⟩

/-- The stage never decreases as actual time advances. -/
theorem stageIndex_monotone (entry : ℕ → ℕ) : Monotone (stageIndex entry) := by
  intro j l hjl
  exact Nat.findGreatest_mono (fun _ h ↦ h.trans hjl) hjl

/-- At one time step the stage either stays fixed or increases by exactly one.
Strictly increasing natural entrance times rule out simultaneous stage jumps. -/
theorem stageIndex_step
    (entry : ℕ → ℕ) (hentry : StrictMono entry) (hzero : entry 0 = 0) (j : ℕ) :
    stageIndex entry (j + 1) = stageIndex entry j ∨
      stageIndex entry (j + 1) = stageIndex entry j + 1 := by
  have hlo : stageIndex entry j ≤ stageIndex entry (j + 1) :=
    stageIndex_monotone entry (Nat.le_succ j)
  have hhi : stageIndex entry (j + 1) ≤ stageIndex entry j + 1 := by
    by_contra hnot
    have hi : stageIndex entry j + 1 < stageIndex entry (j + 1) := by omega
    have hstrict := hentry hi
    have hprev := stageIndex_before_next entry hentry j
    have hnext := stageIndex_entered entry hzero (j + 1)
    omega
  omega

/-- Finite entrance times force the stages to infinity along the FULL time
sequence. No extraction or change of the original scale sequence is involved. -/
theorem tendsto_stageIndex_atTop (entry : ℕ → ℕ) (hentry : StrictMono entry) :
    Tendsto (stageIndex entry) atTop atTop := by
  apply tendsto_atTop.2
  intro k
  refine eventually_atTop.2 ⟨entry k, ?_⟩
  intro j hj
  exact Nat.le_findGreatest ((hentry.id_le k).trans hj) hj

/-- The manuscript numbers its first stage ten. -/
def repairStage (entry : ℕ → ℕ) (j : ℕ) : ℕ := 10 + stageIndex entry j

theorem repairStage_ge_ten (entry : ℕ → ℕ) (j : ℕ) : 10 ≤ repairStage entry j := by
  simp [repairStage]

theorem repairStage_zero (entry : ℕ → ℕ) : repairStage entry 0 = 10 := by
  simp [repairStage, stageIndex]

theorem repairStage_at_entry
    (entry : ℕ → ℕ) (hentry : StrictMono entry) (hzero : entry 0 = 0) (k : ℕ) :
    repairStage entry (entry k) = 10 + k := by
  simp only [repairStage, stageIndex_at_entry entry hentry hzero k]

theorem tendsto_repairStage_atTop (entry : ℕ → ℕ) (hentry : StrictMono entry) :
    Tendsto (repairStage entry) atTop atTop := by
  apply tendsto_atTop_mono (fun j ↦ Nat.le_add_left (stageIndex entry j) 10)
  exact tendsto_stageIndex_atTop entry hentry

/-- The actual next amplitude has exactly one of the paper's two reserve
values: the same-stage `tau^k` or the exit-stage `tau^(k+1)`. -/
theorem repairStage_next_reserve
    (entry : ℕ → ℕ) (hentry : StrictMono entry) (hzero : entry 0 = 0)
    {t : ℝ} (ht : 0 ≤ t) (j : ℕ) :
    iterationScale t (j + 1) ^ repairStage entry (j + 1) =
        (iterationScale t j ^ (6 / 5 : ℝ)) ^ repairStage entry j ∨
    iterationScale t (j + 1) ^ repairStage entry (j + 1) =
        (iterationScale t j ^ (6 / 5 : ℝ)) ^ (repairStage entry j + 1) := by
  rw [iterationScale_succ ht]
  rcases stageIndex_step entry hentry hzero j with h | h
  · left
    simp only [repairStage, h]
  · right
    simp only [repairStage, h, Nat.add_assoc]

/-- The scheduled actual amplitudes vanish by the already proved tenth-power
bound. Unbounded, finite waiting times do not interfere with this conclusion. -/
theorem tendsto_scheduled_repair_defect_zero
    (entry : ℕ → ℕ) {t : ℝ} (ht : 0 < t) (ht1 : t < 1) :
    Tendsto (fun j ↦ iterationScale t j ^ repairStage entry j) atTop (𝓝 0) :=
  tendsto_repair_defect_scale_zero ht ht1 (repairStage entry) (repairStage_ge_ten entry)

#print axioms stageIndex_entered
#print axioms stageIndex_before_next
#print axioms stageIndex_eq_iff
#print axioms stageIndex_at_entry
#print axioms stageIndex_monotone
#print axioms stageIndex_step
#print axioms tendsto_stageIndex_atTop
#print axioms repairStage_ge_ten
#print axioms repairStage_zero
#print axioms repairStage_at_entry
#print axioms tendsto_repairStage_atTop
#print axioms repairStage_next_reserve
#print axioms tendsto_scheduled_repair_defect_zero

end GlobalEmbedding.Offline
