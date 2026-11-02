import Probes.Round3RepairBlockDisplacement

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
local instance round3RepairBlockPieceChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairBlockPieceIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)









namespace Round3RepairConstructedBlock
variable [CompactSpace M]
  {cost : Round3RepairPrimitiveCosts} {Cpair : ℕ → ℝ}
  {budget epsilon eta : ℝ} {k : ℕ} {hk : 10 ≤ k}
  {t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta k t}
  {capNext : ℝ} {start : ℕ}
  (block : Round3RepairConstructedBlock (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cpair budget epsilon eta k hk t ht ht1 initial capNext start)


/-- Each full-time piece is the genuine mean-corrected sine/cosine U and
inherits its original growing-order estimate, including the advancing U. -/
theorem piece_control (micro : ℕ) (hmicro : micro ≤ block.waitIndex)
    (heps : 0 < epsilon) (htDisp : t ≤ epsilon/(8*(cost.Cmap (k/2)+1)))
    (htTheta : t < cost.Theta^10) :
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (block.piece packet micro) ∧
    paperAtlasCj (k/2) (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (block.piece packet micro))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal ((epsilon/8)*iterationScale t micro) := by
  have htj (j : ℕ) : iterationScale t j ≤ t :=
    Real.rpow_le_self_of_le_one ht.le ht1.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))
  have hout (j : ℕ) := round3_repair_state_primitive_conclusion packet cost (block.states j) k hk le_rfl
    (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le (block.primitive j) ((htj j).trans_lt htTheta)
  have hAdvance := round3_repair_state_primitive_conclusion packet cost (block.states block.waitIndex) (k+1) hk (Nat.le_succ k)
    (iterationScale_pos ht block.waitIndex) (iterationScale_lt_one ht.le ht1 block.waitIndex).le
    block.advancing ((htj block.waitIndex).trans_lt htTheta)
  have hSmooth (j : ℕ) : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (block.piece packet j) := by
    unfold piece
    split_ifs
    · rw [modelWithCornersSelf_prod]
      exact contMDiffOn_univ.mp (hout j).joint_smooth
    · rw [modelWithCornersSelf_prod]
      exact contMDiffOn_univ.mp hAdvance.joint_smooth
  have hBound (j : ℕ) (hj : j ∈ Finset.range (block.waitIndex+1)) :
      paperAtlasCj (k/2) (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (block.piece packet j))
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal ((epsilon/8)*iterationScale t j) := by
    by_cases hlt : j < block.waitIndex
    · simp only [piece,if_pos hlt]
      exact round3Parameter_same_increment_growing_order_budget Data.atlas packet.parameterFamily.chart packet.closedSamples
        univ _ _ _ (40*(k+1)) (iterationScale t j^k) ((iterationScale t j)^(6/5 : ℝ))
        ((iterationScale t j)^(11/10 : ℝ)) cost.Cmap cost.Cmetric cost.map_nonneg (hout j)
        (iterationScale t j) (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le k hk rfl rfl
        epsilon ((htj j).trans htDisp)
    · have heq : j = block.waitIndex := by simp only [Finset.mem_range] at hj; omega
      subst j
      simp only [piece,lt_self_iff_false,if_false]
      exact round3Parameter_same_increment_growing_order_budget Data.atlas packet.parameterFamily.chart packet.closedSamples
        univ _ _ _ (40*(k+1)) (iterationScale t block.waitIndex^k) ((iterationScale t block.waitIndex)^(6/5 : ℝ))
        ((iterationScale t block.waitIndex)^(11/10 : ℝ)) cost.Cmap cost.Cmetric cost.map_nonneg hAdvance
        (iterationScale t block.waitIndex) (iterationScale_pos ht block.waitIndex)
        (iterationScale_lt_one ht.le ht1 block.waitIndex).le k hk rfl rfl
        epsilon ((htj block.waitIndex).trans htDisp)

  exact ⟨hSmooth micro,hBound micro (by simpa using hmicro)⟩
end Round3RepairConstructedBlock
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairConstructedBlock.piece_control
