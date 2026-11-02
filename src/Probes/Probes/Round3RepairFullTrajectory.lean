import Probes.Round3RepairInitialToMetric

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
universe uTr uΛ uΒ uSubSecondary
variable {Tr : Type uTr} {Λ : Type uΛ} {Β : Type uΒ} {SubSecondary : Type uSubSecondary}
  [NormedAddCommGroup Tr] [NormedSpace ℝ Tr]
  [Fintype Λ] [DecidableEq Λ] [Fintype Β] [Fintype SubSecondary]
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairFullTrajectoryChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairFullTrajectoryIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)











namespace Round3RepairInfiniteBlocks
variable [CompactSpace M]
  {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
  (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta t ht ht1 initial)

def entries : ℕ → ℕ := fun r => (run.entry r).index

theorem entries_zero : run.entries packet 0 = 0 := run.initial_index

theorem entries_strictMono : StrictMono (run.entries packet) :=
  strictMono_nat_of_lt_succ fun r => by
    change (run.entry r).index < (run.entry (r+1)).index
    rw [run.next_index r]
    omega

def level (j : ℕ) := stageIndex (run.entries packet) j

def stage (j : ℕ) := repairStage (run.entries packet) j

def localIndex (j : ℕ) := j-run.entries packet (run.level packet j)

theorem entered (j : ℕ) : run.entries packet (run.level packet j) ≤ j :=
  stageIndex_entered (run.entries packet) (run.entries_zero packet) j

theorem before_next (j : ℕ) : j < run.entries packet (run.level packet j+1) :=
  stageIndex_before_next (run.entries packet) (run.entries_strictMono packet) j

theorem localIndex_le_wait (j : ℕ) : run.localIndex packet j ≤ (run.block (run.level packet j)).waitIndex := by
  have h := run.before_next packet j
  have he := run.entered packet j
  change j < (run.entry (run.level packet j+1)).index at h
  rw [run.next_index] at h
  change j-(run.entry (run.level packet j)).index ≤ _
  omega

theorem localScale_eq (j : ℕ) :
    iterationScale (iterationScale t (run.entries packet (run.level packet j))) (run.localIndex packet j) = iterationScale t j := by
  rw [← iterationScale_add ht.le]
  congr 1
  exact Nat.add_sub_of_le (run.entered packet j)

/-- Every natural time has the actual local block state, on the original
unchanged scale t_j.  Transport changes only the proof of the scale index. -/
def state (j : ℕ) : Round3RepairClosedState packet budget epsilon eta (run.stage packet j) (iterationScale t j) :=
  ((run.block (run.level packet j)).states (run.localIndex packet j)).atEqualScale packet (run.localScale_eq packet j)

def increment (j : ℕ) : P × M → Ey :=
  (run.block (run.level packet j)).piece packet (run.localIndex packet j)

@[simp] theorem state_map (j : ℕ) : (run.state packet j).map =
    ((run.block (run.level packet j)).states (run.localIndex packet j)).map :=
  Round3RepairClosedState.atEqualScale_map packet _ _

theorem level_succ_of_stay (j : ℕ)
    (hStay : run.localIndex packet j < (run.block (run.level packet j)).waitIndex) :
    run.level packet (j+1) = run.level packet j := by
  apply (stageIndex_eq_iff (run.entries packet) (run.entries_strictMono packet) (run.entries_zero packet) _ _).mpr
  refine ⟨(run.entered packet j).trans (Nat.le_succ j),?_⟩
  change j+1 < (run.entry (run.level packet j+1)).index
  rw [run.next_index]
  have he := run.entered packet j
  change j-(run.entry (run.level packet j)).index < _ at hStay
  change (run.entry (run.level packet j)).index ≤ j at he
  omega

theorem level_succ_of_advance (j : ℕ)
    (hAdvance : run.localIndex packet j = (run.block (run.level packet j)).waitIndex) :
    run.level packet (j+1) = run.level packet j+1 := by
  have he := run.entered packet j
  have hEntry : j+1 = run.entries packet (run.level packet j+1) := by
    change j+1 = (run.entry (run.level packet j+1)).index
    rw [run.next_index]
    change j-(run.entry (run.level packet j)).index = _ at hAdvance
    change (run.entry (run.level packet j)).index ≤ j at he
    omega
  change stageIndex (run.entries packet) (j+1) = _
  rw [hEntry]
  exact stageIndex_at_entry _ (run.entries_strictMono packet) (run.entries_zero packet) _

theorem localIndex_succ_of_stay (j : ℕ)
    (hStay : run.localIndex packet j < (run.block (run.level packet j)).waitIndex) :
    run.localIndex packet (j+1) = run.localIndex packet j+1 := by
  unfold localIndex
  rw [run.level_succ_of_stay packet j hStay]
  have he := run.entered packet j
  omega

theorem localIndex_succ_of_advance (j : ℕ)
    (hAdvance : run.localIndex packet j = (run.block (run.level packet j)).waitIndex) :
    run.localIndex packet (j+1) = 0 := by
  unfold localIndex
  rw [run.level_succ_of_advance packet j hAdvance]
  change j+1-(run.entry (run.level packet j+1)).index = 0
  rw [run.next_index]
  change j-(run.entry (run.level packet j)).index = _ at hAdvance
  omega

/-- The full-time physical trajectory uses the actual U of its original
block at every step, including the genuine advancing step. -/
theorem actual_update (j : ℕ) :
    (run.state packet (j+1)).map = fun z => (run.state packet j).map z+run.increment packet j z := by
  rw [run.state_map packet (j+1),run.state_map packet j]
  by_cases hStay : run.localIndex packet j < (run.block (run.level packet j)).waitIndex
  · rw [run.level_succ_of_stay packet j hStay,run.localIndex_succ_of_stay packet j hStay]
    rw [(run.block (run.level packet j)).update]
    simp only [increment,Round3RepairConstructedBlock.piece,if_pos hStay]
  · have hAdvance : run.localIndex packet j = (run.block (run.level packet j)).waitIndex :=
      le_antisymm (run.localIndex_le_wait packet j) (Nat.le_of_not_gt hStay)
    rw [run.level_succ_of_advance packet j hAdvance,run.localIndex_succ_of_advance packet j hAdvance,
      (run.block (run.level packet j+1)).initial_map,run.next_map,(run.block (run.level packet j)).next_map]
    simp only [increment,Round3RepairConstructedBlock.piece,hAdvance,lt_self_iff_false,if_false]
    rw [show ((run.block (run.level packet j)).states (run.localIndex packet j)).map =
        ((run.block (run.level packet j)).states (run.block (run.level packet j)).waitIndex).map from
      congrArg (fun a => ((run.block (run.level packet j)).states a).map) hAdvance]

theorem full_stage_tendsto : Tendsto (run.stage packet) atTop atTop :=
  tendsto_repairStage_atTop _ (run.entries_strictMono packet)

theorem full_stage_ge_ten (j : ℕ) : 10 ≤ run.stage packet j := repairStage_ge_ten _ _

theorem full_stage_step (j : ℕ) : run.stage packet (j+1) = run.stage packet j ∨
    run.stage packet (j+1) = run.stage packet j+1 := by
  rcases stageIndex_step (run.entries packet) (run.entries_strictMono packet) (run.entries_zero packet) j with h | h
  · left; simp only [stage,repairStage,h]
  · right; simp only [stage,repairStage,h,Nat.add_assoc]

theorem initial_state_map : (run.state packet 0).map = initial.map := by
  rw [run.state_map]
  have hlevel : run.level packet 0 = 0 := by simp [level,stageIndex]
  have hlocal : run.localIndex packet 0 = 0 := by simp [localIndex]
  rw [hlevel,hlocal,(run.block 0).initial_map,run.initial_map]

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.actual_update
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.full_stage_tendsto
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.initial_state_map
