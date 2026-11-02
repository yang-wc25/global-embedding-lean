import Probes.Round3RepairFullJets
import Probes.Round3RepairBlockJoint

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold Filter
open scoped ContDiff ENNReal Topology
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
local instance round3RepairFullJointChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairFullJointIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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

theorem full_stage_le_next (j : ℕ) : run.stage packet j ≤ run.stage packet (j+1) := by
  rcases run.full_stage_step packet j with h | h <;> omega

/-- At every original natural time, the actual U has its complete all-order
conclusion and (6.8) for the literal SF/SH computed from the actual current
state and its actual next stage.  This is one full-time trajectory, including
both stay and advancing updates, with no fresh U choice after flattening. -/
theorem full_joint_conclusion
    (hTheta : ∀ r, sigma r < (cost r).Theta^10) (j : ℕ) :
    let current := (run.state packet j).toSmoothingState (run.stage packet (j+1))
      (run.full_stage_ge_ten packet j) (run.full_stage_le_next packet j)
      (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      (current.smoothedMap packet) (run.increment packet j) (current.computedTarget packet)
      (40*(run.stage packet j+1)) (iterationScale t j^run.stage packet j)
      ((iterationScale t j)^(6/5 : ℝ)) ((iterationScale t j)^(11/10 : ℝ))
      (cost (run.level packet j)).Cmap (cost (run.level packet j)).Cmetric := by
  let r := run.level packet j
  let a := run.localIndex packet j
  let block := run.block r
  let s := if a < block.waitIndex then 10+r else 10+r+1
  have hks : 10+r ≤ s := by dsimp only [s]; split_ifs <;> omega
  have hNext : s=run.stage packet (j+1) := by
    dsimp only [s]
    by_cases hStay : a < block.waitIndex
    · rw [if_pos hStay]
      have hl := run.level_succ_of_stay packet j hStay
      change 10+run.level packet j = 10+run.level packet (j+1)
      rw [hl]
    · have hAdvance : a=block.waitIndex :=
        le_antisymm (run.localIndex_le_wait packet j) (Nat.le_of_not_gt hStay)
      rw [if_neg hStay]
      have hl := run.level_succ_of_advance packet j hAdvance
      change 10+run.level packet j+1 = 10+run.level packet (j+1)
      rw [hl]
      omega
  have hOut := block.piece_joint_conclusion packet a (run.localIndex_le_wait packet j)
    ((run.entry r).admissible.trans_lt (hTheta r)) hks
  exact round3_repair_joint_transfer packet (block.states a) (run.state packet j)
    (run.full_stage_ge_ten packet j) hks (run.full_stage_le_next packet j)
    (iterationScale_pos (iterationScale_pos ht (run.entry r).index) a)
    (iterationScale_lt_one (iterationScale_pos ht (run.entry r).index).le
      (iterationScale_lt_one ht.le ht1 (run.entry r).index) a).le
    (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le
    (run.localScale_eq packet j) hNext (run.state_map packet j).symm
    (run.increment packet j) (cost r).Cmap (cost r).Cmetric hOut

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.full_joint_conclusion
