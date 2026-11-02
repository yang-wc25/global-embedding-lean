import Probes.Round3RepairBlockPieceControl

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
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
local instance round3RepairBlockJointChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairBlockJointIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)









/-- Changing equal scale/next-stage indices and proof fields preserves the
literal pair of smoothing formulas.  The physical map is required equal. -/
theorem round3_repair_joint_transfer [CompactSpace M]
    {budget epsilon eta : ℝ} {k s s' : ℕ} {v v' : ℝ}
    (left : Round3RepairClosedState packet budget epsilon eta k v)
    (right : Round3RepairClosedState packet budget epsilon eta k v')
    (hk : 10 ≤ k) (hks : k ≤ s) (hks' : k ≤ s')
    (hv : 0 < v) (hv1 : v ≤ 1) (hv' : 0 < v') (hv1' : v' ≤ 1)
    (hScale : v=v') (hNext : s=s') (hMap : left.map=right.map)
    (U : P × M → Ey) (Cmap Cmetric : ℕ → ℝ)
    (hOut : Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      ((left.toSmoothingState s hk hks hv hv1).smoothedMap packet) U
      ((left.toSmoothingState s hk hks hv hv1).computedTarget packet)
      (40*(k+1)) (v^k) (v^(6/5 : ℝ)) (v^(11/10 : ℝ)) Cmap Cmetric) :
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      ((right.toSmoothingState s' hk hks' hv' hv1').smoothedMap packet) U
      ((right.toSmoothingState s' hk hks' hv' hv1').computedTarget packet)
      (40*(k+1)) (v'^k) (v'^(6/5 : ℝ)) (v'^(11/10 : ℝ)) Cmap Cmetric := by
  subst v'
  subst s'
  have hState : left=right := by
    cases left
    cases right
    cases hMap
    rfl
  subst right
  exact hOut

namespace Round3RepairConstructedBlock
variable [CompactSpace M]
  {cost : Round3RepairPrimitiveCosts} {Cpair : ℕ → ℝ}
  {budget epsilon eta : ℝ} {k : ℕ} {hk : 10 ≤ k}
  {t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta k t}
  {capNext : ℝ} {start : ℕ}
  (block : Round3RepairConstructedBlock (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cpair budget epsilon eta k hk t ht ht1 initial capNext start)

/-- The complete all-order conclusion and (6.8) of each actual finite-block
piece, at its actual stay or advancing next stage. -/
theorem piece_joint_conclusion (micro : ℕ) (hmicro : micro ≤ block.waitIndex)
    (htTheta : t < cost.Theta^10) :
    let s := if micro < block.waitIndex then k else k+1
    ∀ hks : k ≤ s,
    let current := (block.states micro).toSmoothingState s hk hks
      (iterationScale_pos ht micro) (iterationScale_lt_one ht.le ht1 micro).le
    Round3ParameterJointIncrementConclusion Data.atlas packet.parameterFamily.chart packet.closedSamples univ
      (current.smoothedMap packet) (block.piece packet micro) (current.computedTarget packet)
      (40*(k+1)) (iterationScale t micro^k) ((iterationScale t micro)^(6/5 : ℝ))
      ((iterationScale t micro)^(11/10 : ℝ)) cost.Cmap cost.Cmetric := by
  have htj (j : ℕ) : iterationScale t j ≤ t :=
    Real.rpow_le_self_of_le_one ht.le ht1.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))
  dsimp only
  by_cases hStay : micro < block.waitIndex
  · simp only [if_pos hStay]
    intro hks
    have h := round3_repair_state_primitive_conclusion packet cost (block.states micro) k hk le_rfl
      (iterationScale_pos ht micro) (iterationScale_lt_one ht.le ht1 micro).le
      (block.primitive micro) ((htj micro).trans_lt htTheta)
    simpa only [piece,if_pos hStay] using h
  · have hAdvance : micro=block.waitIndex := by omega
    subst micro
    simp only [lt_self_iff_false,if_false]
    intro hks
    have h := round3_repair_state_primitive_conclusion packet cost (block.states block.waitIndex) (k+1) hk (Nat.le_succ k)
      (iterationScale_pos ht block.waitIndex) (iterationScale_lt_one ht.le ht1 block.waitIndex).le
      block.advancing ((htj block.waitIndex).trans_lt htTheta)
    simpa only [piece,lt_self_iff_false,if_false] using h

end Round3RepairConstructedBlock
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_joint_transfer
#print axioms GlobalEmbedding.Continuation.Round3RepairConstructedBlock.piece_joint_conclusion
