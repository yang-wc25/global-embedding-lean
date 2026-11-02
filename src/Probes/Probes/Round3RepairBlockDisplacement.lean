import Probes.Round3RepairConstructedBlock

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
local instance round3RepairBlockDisplacementChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairBlockDisplacementIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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

def piece (j : ℕ) : P × M → Ey :=
  if j < block.waitIndex then (block.primitive j).increment packet else block.advancing.increment packet

def increment : P × M → Ey := fun z => ∑ j ∈ Finset.range (block.waitIndex+1), block.piece packet j z

/-- The block increment is the actual finite sum of its recorded sine/cosine
increments, with one terminal advancing increment. -/
theorem next_map_eq_increment : block.next.map = fun z => initial.map z+block.increment packet z := by
  have hTel (j : ℕ) (hj : j ≤ block.waitIndex) :
      (block.states j).map = fun z => initial.map z+∑ a ∈ Finset.range j, block.piece packet a z := by
    induction j with
    | zero => simpa using block.initial_map
    | succ j ih =>
      rw [block.update j,ih (by omega)]
      funext z
      simp only [Finset.sum_range_succ,piece,if_pos (show j < block.waitIndex by omega)]
      abel
  rw [block.next_map,hTel block.waitIndex le_rfl]
  funext z
  simp only [increment,Finset.sum_range_succ,piece,lt_self_iff_false,if_false]
  abel

/-- Every block displacement has a growing original-order budget, derived
from each actual primitive U and the finite total scale budget. -/
theorem displacement_budget
    (heps : 0 < epsilon) (htSmall : t ≤ (1/2 : ℝ)^5)
    (htDisp : t ≤ epsilon/(8*(cost.Cmap (k/2)+1))) (htTheta : t < cost.Theta^10) :
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (block.increment packet) ∧
    paperAtlasCj (k/2) (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (block.increment packet))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal ((epsilon/4)*t) := by
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
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hTotal : (∑ j ∈ Finset.range (block.waitIndex+1), (epsilon/8)*iterationScale t j) ≤ (epsilon/4)*t := by
    have hFin := ((summable_iterationScale ht ht1).mul_left (epsilon/8)).sum_le_tsum
      (Finset.range (block.waitIndex+1)) (fun j _ => mul_nonneg (by positivity) (iterationScale_pos ht j).le)
    rw [tsum_mul_left] at hFin
    have hScale : (∑' j, iterationScale t j) ≤ 2*t := by
      simpa only [Real.rpow_one] using tsum_iterationScale_power_le_twice_of_small ht htSmall
        (p := 1) (by norm_num : (1:ℝ) ≤ 1)
    exact hFin.trans ((mul_le_mul_of_nonneg_left hScale (by positivity)).trans_eq (by ring))
  refine ⟨ContMDiff.sum (fun j _ => hSmooth j),?_⟩
  apply iSup_le
  intro i
  have hEq : incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (block.increment packet) i =
      fun y => ∑ j ∈ Finset.range (block.waitIndex+1),
        incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (block.piece packet j) i y := by
    funext y
    simp only [increment,incrementsOriginalMapCoordinates,map_sum]
  rw [hEq]
  apply le_trans _ (ENNReal.ofReal_le_ofReal hTotal)
  apply paperCoordinateCj_sum_le (k/2)
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
    (fun _ hy => hy.1) (Finset.range (block.waitIndex+1))
    (fun j => incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (block.piece packet j) i)
    (fun j _ => parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB _ (hSmooth j) i)
    (fun j => (epsilon/8)*iterationScale t j)
    (fun j _ => mul_nonneg (by positivity) (iterationScale_pos ht j).le)
  intro j hj
  exact (le_iSup (fun a => paperCoordinateCj (k/2)
    (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (block.piece packet j) a)
    (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart a) (packet.closedSamples a)) i).trans (hBound j hj)

end Round3RepairConstructedBlock
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairConstructedBlock.next_map_eq_increment
#print axioms GlobalEmbedding.Continuation.Round3RepairConstructedBlock.displacement_budget
