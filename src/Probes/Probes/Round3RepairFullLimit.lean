import Probes.Round3RepairFullTrajectory
import Probes.Round3RepairBlockPieceControl
import Smoothing.Round3RepairOriginalMetricLimit

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
local instance round3RepairFullLimitChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairFullLimitIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)












/-- The actual full-time repair limit, including the original C2 reserve.
Its U_j is the single literal oscillatory choice at that microstep. -/
def Round3RepairFullLimitConclusion [CompactSpace M]
    {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
    {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
    {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
    (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial) : Prop :=
    let u := run.increment packet
    let Fstar := fun z => initial.map z+∑' j, u j z
    (∀ z, Summable (fun j => u j z)) ∧
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ Fstar ∧
    (∀ p, inducedMetric (I := IT) (fun x => Fstar (p,x)) = packet.metric p) ∧
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => Fstar z-initial.map z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples < ENNReal.ofReal (epsilon/8) ∧
    packet.mapDistance Fstar ≠ ⊤ ∧ (packet.mapDistance Fstar).toReal < 3*epsilon/8

namespace Round3RepairInfiniteBlocks
variable [CompactSpace M]
  {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
  {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
  {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
  (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
    packet cost Cs sigma budget epsilon eta t ht ht1 initial)

theorem full_increment_control
    (heps : 0 < epsilon)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10) (j : ℕ) :
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (run.increment packet j) ∧
    paperAtlasCj (run.stage packet j/2)
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (run.increment packet j))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal ((epsilon/8)*iterationScale t j) := by
  have h := (run.block (run.level packet j)).piece_control packet (run.localIndex packet j)
    (run.localIndex_le_wait packet j) heps
    ((run.entry (run.level packet j)).admissible.trans (hDisp _))
    ((run.entry (run.level packet j)).admissible.trans_lt (hTheta _))
  have hScale := run.localScale_eq packet j
  change iterationScale (iterationScale t (run.entry (run.level packet j)).index) (run.localIndex packet j) =
    iterationScale t j at hScale
  rw [hScale] at h
  exact h

/-- The genuine natural-time trajectory, with its original t_j, reaches one
jointly smooth exact-metric limit.  All analytic budgets are extracted from
its actual primitive U_j, and every stage advance is the proved finite one. -/
theorem full_metric_limit
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10) :
    Round3RepairFullLimitConclusion packet run := by
  have htSmall : t ≤ (1/2 : ℝ)^5 := by
    have h := (run.entry 0).admissible.trans (hSmall 0)
    simpa only [run.initial_index,iterationScale_zero] using h
  have hActual := run.full_increment_control packet heps hDisp hTheta
  have h := round3_repair_closed_original_metric_limit packet hK budget epsilon eta t (epsilon/8)
    heps ht htSmall (by positivity) (run.stage packet) (run.full_stage_tendsto packet)
    (run.full_stage_ge_ten packet) (run.state packet) (run.increment packet)
    (fun j => (hActual j).1) (run.actual_update packet) (fun j => (hActual j).2)
  have hEq : epsilon/4+epsilon/8 = 3*epsilon/8 := by ring
  simpa only [Round3RepairFullLimitConclusion,run.initial_state_map packet,hEq] using h

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.full_increment_control
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.full_metric_limit
