import Probes.Round3RepairFullTrajectory
import Probes.Round4ParameterProbeTailCaps

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
local instance round4ParameterProbeBlockChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterProbeBlockIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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

/-- The genuine stay/advance U retains its fixed-order original atlas bound.
The derivative order is independent of the growing stage. -/
theorem probe_original_fixed_order (a micro : ℕ) (hmicro : micro ≤ block.waitIndex)
    (htTheta : t < cost.Theta^10) :
    paperAtlasCj a (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (block.piece packet micro))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal (cost.Cmap a * iterationScale t micro^k *
        iterationScale t micro^(6/5 : ℝ)/(iterationScale t micro^(6/5 : ℝ))^a) := by
  have htj (j : ℕ) : iterationScale t j ≤ t :=
    Real.rpow_le_self_of_le_one ht.le ht1.le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))
  by_cases hlt : micro < block.waitIndex
  · have hout := round3_repair_state_primitive_conclusion packet cost (block.states micro) k hk le_rfl
      (iterationScale_pos ht micro) (iterationScale_lt_one ht.le ht1 micro).le
      (block.primitive micro) ((htj micro).trans_lt htTheta)
    simp only [piece,ite_eq_left hlt]
    exact round4ParameterProbe_unweight_original a (a+1) (by omega) _ _
      (Real.rpow_pos_of_pos (iterationScale_pos ht micro) _)
      _ _ _ (hout.map0 a).1 (hout.map0 a).2
  · have heq : micro = block.waitIndex := by omega
    subst micro
    have hout := round3_repair_state_primitive_conclusion packet cost (block.states block.waitIndex) (k+1) hk (Nat.le_succ k)
      (iterationScale_pos ht block.waitIndex) (iterationScale_lt_one ht.le ht1 block.waitIndex).le
      block.advancing ((htj block.waitIndex).trans_lt htTheta)
    simp only [piece,lt_self_iff_false,ite_false]
    exact round4ParameterProbe_unweight_original a (a+1) (by omega) _ _
      (Real.rpow_pos_of_pos (iterationScale_pos ht block.waitIndex) _)
      _ _ _ (hout.map0 a).1 (hout.map0 a).2

end Round3RepairConstructedBlock

namespace Round3RepairInfiniteBlocks
variable [CompactSpace M]
  {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
  (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta t ht ht1 initial)

/-- The finite cap acts on the same full-time run, including every actual
waiting step. It yields the exact order-dependent powers used by (8.4). -/
theorem probe_increment_original_order
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (a : ℕ) (ha : 1 ≤ a) (ha3 : a ≤ 3) (j : ℕ) :
    paperAtlasCj a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (run.increment packet j))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal (round4ParameterProbeTailConstant cost *
        iterationScale t j^((10 : ℝ)+(6/5 : ℝ)*(1-(a : ℝ)))) := by
  have h := (run.block (run.level packet j)).probe_original_fixed_order packet a
    (run.localIndex packet j) (run.localIndex_le_wait packet j)
    ((run.entry (run.level packet j)).admissible.trans_lt (hTheta _))
  have hScale := run.localScale_eq packet j
  change iterationScale (iterationScale t (run.entry (run.level packet j)).index) (run.localIndex packet j) =
    iterationScale t j at hScale
  rw [hScale,round4ParameterProbe_fixed_order_power (iterationScale_pos ht j)] at h
  have hvCap : iterationScale t j ≤ round4ParameterProbeTailCap cost (run.level packet j) := by
    rw [← hScale]
    exact (Real.rpow_le_self_of_le_one (iterationScale_pos ht _).le
      (iterationScale_lt_one ht.le ht1 _).le (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))).trans
      ((run.entry _).admissible.trans (hCap _))
  exact h.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right
    (round4ParameterProbeTailCap_absorbs cost (run.level packet j) a ha ha3
      (iterationScale_pos ht j) (iterationScale_lt_one ht.le ht1 j).le hvCap)
    (Real.rpow_nonneg (iterationScale_pos ht j).le _)))

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairConstructedBlock.probe_original_fixed_order
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.probe_increment_original_order
