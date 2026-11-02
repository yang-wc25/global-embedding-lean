import Probes.Round4ParameterProbeSameRunTail
import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

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
local instance round4ActualRepairResponseChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ActualRepairResponseIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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

/-! Explicit vanishing moduli for the same actual repair tail. The scale
parameter need not be a differentiable argument of the constructed family. -/

def round4RepairHessianTailModulus (C s : ℝ) : ℝ := 2*C*s^(8/25 : ℝ)
def round4RepairCOneTailModulus (C s : ℝ) : ℝ := 2*C*s^(14/25 : ℝ)
def round4RepairValueTailModulus (C s : ℝ) : ℝ := 2*C*s^(4/5 : ℝ)

private theorem tail_modulus_tendsto_zero (C q : ℝ) (hq : 0 < q) :
    Tendsto (fun s : ℝ => 2*C*s^q) (𝓝 0) (𝓝 0) := by
  have hc : Continuous (fun s : ℝ => 2*C*s^q) :=
    continuous_const.mul (Real.continuous_rpow_const hq.le)
  simpa only [Real.zero_rpow hq.ne',mul_zero] using hc.tendsto 0

theorem round4_repair_response_moduli_tendsto_zero (C : ℝ) :
    Tendsto (round4RepairHessianTailModulus C) (𝓝 0) (𝓝 0) ∧
    Tendsto (round4RepairCOneTailModulus C) (𝓝 0) (𝓝 0) ∧
    Tendsto (round4RepairValueTailModulus C) (𝓝 0) (𝓝 0) := by
  exact ⟨tail_modulus_tendsto_zero C _ (by norm_num),
    tail_modulus_tendsto_zero C _ (by norm_num),
    tail_modulus_tendsto_zero C _ (by norm_num)⟩

theorem round4_repair_response_moduli_nonneg {C s : ℝ} (hC : 0 ≤ C) (hs : 0 ≤ s) :
    0 ≤ round4RepairHessianTailModulus C s ∧
    0 ≤ round4RepairCOneTailModulus C s ∧
    0 ≤ round4RepairValueTailModulus C s := by
  unfold round4RepairHessianTailModulus round4RepairCOneTailModulus round4RepairValueTailModulus
  exact ⟨by positivity,by positivity,by positivity⟩

/-- The original mixed tail on the SAME actual trajectory is small relative
respectively to the Hessian response sigma=s^(44/5), the C1 scale s^10,
and the displacement response a=s^(56/5). No requested tail bound is input. -/
theorem probe_mixed_tail_response_moduli
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ)) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    let tail := fun z => Fstar z-initial.map z
    let C := round4ParameterProbeTailConstant cost
    (⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) 2 1
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) ≤
        ENNReal.ofReal (s^(44/5 : ℝ)*round4RepairHessianTailModulus C s) ∧
    (⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) 1 1
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) ≤
        ENNReal.ofReal (s^(10 : ℝ)*round4RepairCOneTailModulus C s) ∧
    (⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) 0 1
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) ≤
        ENNReal.ofReal (s^(56/5 : ℝ)*round4RepairValueTailModulus C s) := by
  intro Fstar tail C
  have hfactor (a b : ℝ) : s^a*(2*C*s^b) = 2*C*s^(a+b) := by
    calc
      s^a*(2*C*s^b) = 2*C*(s^a*s^b) := by ring
      _ = 2*C*s^(a+b) := by rw [Real.rpow_add hs]
  have h3 : s^(44/5 : ℝ)*round4RepairHessianTailModulus C s =
      2*C*s^(228/25 : ℝ) := by
    unfold round4RepairHessianTailModulus
    convert hfactor (44/5) (8/25) using 1; norm_num
  have h2 : s^(10 : ℝ)*round4RepairCOneTailModulus C s =
      2*C*s^(264/25 : ℝ) := by
    unfold round4RepairCOneTailModulus
    convert hfactor 10 (14/25) using 1; norm_num
  have h1 : s^(56/5 : ℝ)*round4RepairValueTailModulus C s =
      2*C*s^(12 : ℝ) := by
    unfold round4RepairValueTailModulus
    convert hfactor (56/5) (4/5) using 1; norm_num
  rw [h3,h2,h1]
  exact run.probe_mixed_tail_84 packet hK heps hSmall hDisp hTheta hCap s hs hstart

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.round4_repair_response_moduli_tendsto_zero
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.probe_mixed_tail_response_moduli
