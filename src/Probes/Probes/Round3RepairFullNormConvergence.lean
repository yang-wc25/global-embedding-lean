import Probes.Round3RepairFullJets
import Smoothing.Round3RepairOriginalSumBound

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
local instance round3RepairFullNormConvergenceChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairFullNormConvergenceIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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

/-- Beyond the actual stage needed for order a, every full-time tail has
its original closed Ω/Q C^a norm bounded by the same scalar t_J. The proof
passes the actual coordinate jets to the original MAX without atlas losses. -/
theorem full_original_norm_tail
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10) (a : ℕ) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    ∃ J0 : ℕ, ∀ J, J0 ≤ J →
      paperAtlasCj a (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => Fstar z-(run.state packet J).map z))
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal ((epsilon/4)*iterationScale t J) := by
  intro Fstar
  have htSmall : t ≤ (1/2 : ℝ)^5 := by
    have h := (run.entry 0).admissible.trans (hSmall 0)
    simpa only [run.initial_index,iterationScale_zero] using h
  have hActual := run.full_increment_control packet heps hDisp hTheta
  have hLimit := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  obtain ⟨J0,hJ0⟩ := eventually_atTop.mp ((run.full_stage_tendsto packet).eventually_ge_atTop (2*a))
  refine ⟨J0,?_⟩
  intro J hJ
  have htJ : 0 < iterationScale t J := iterationScale_pos ht J
  have htJ1 : iterationScale t J < 1 := iterationScale_lt_one ht.le ht1 J
  have htJSmall : iterationScale t J ≤ (1/2 : ℝ)^5 :=
    (Real.rpow_le_self_of_le_one ht.le ht1.le
      (one_le_pow₀ (by norm_num : (1:ℝ) ≤ 6/5))).trans htSmall
  have hShiftScale (j : ℕ) : iterationScale (iterationScale t J) j = iterationScale t (j+J) := by
    rw [← iterationScale_add ht.le,Nat.add_comm J j]
  have hBound := round3_repair_closed_original_sum_bound packet hK
    (fun j => run.increment packet (j+J)) (fun j => run.stage packet (j+J))
    (fun j => (hActual (j+J)).1)
    ((run.full_stage_tendsto packet).comp (tendsto_add_atTop_nat J))
    (fun j => (show 4 ≤ 10 by norm_num).trans (run.full_stage_ge_ten packet (j+J)))
    a (fun j => hJ0 (j+J) (by omega))
    (iterationScale t J) (epsilon/8) htJ htJSmall (by positivity)
    (fun j => by rw [hShiftScale]; exact (hActual (j+J)).2)
  have hSum : (∑' j, iterationScale (iterationScale t J) j) ≤ 2*iterationScale t J := by
    simpa only [Real.rpow_one] using
      tsum_iterationScale_power_le_twice_of_small htJ htJSmall (p := 1) (by norm_num : (1:ℝ) ≤ 1)
  have hNum : (epsilon/8)*(∑' j, iterationScale (iterationScale t J) j) ≤
      (epsilon/4)*iterationScale t J := by
    have h := mul_le_mul_of_nonneg_left hSum (by positivity : 0 ≤ epsilon/8)
    nlinarith only [h]
  have hTail : (fun z => Fstar z-(run.state packet J).map z) =
      (fun z => ∑' j, run.increment packet (j+J) z) := by
    funext z
    rw [run.actual_partial_sum packet J]
    have h := (hLimit.1 z).sum_add_tsum_nat_add J
    dsimp only [Fstar]
    rw [← h]
    abel
  rw [hTail]
  exact hBound.trans (ENNReal.ofReal_le_ofReal hNum)

/-- The SAME full repair sequence converges in every original joint C^a
MAX norm on the fixed closed convolution sampling domains. -/
theorem full_original_norm_convergence
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    ∀ a, Tendsto (fun J => paperAtlasCj a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => Fstar z-(run.state packet J).map z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples)
      atTop (𝓝 0) := by
  intro Fstar a
  obtain ⟨J0,hTail⟩ := run.full_original_norm_tail packet hK heps hSmall hDisp hTheta a
  have hBound : ∀ᶠ J in atTop, paperAtlasCj a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => Fstar z-(run.state packet J).map z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal ((epsilon/4)*iterationScale t J) :=
    eventually_atTop.mpr ⟨J0,hTail⟩
  have hZero : Tendsto (fun J => ENNReal.ofReal ((epsilon/4)*iterationScale t J)) atTop (𝓝 0) := by
    simpa only [mul_zero,ENNReal.ofReal_zero] using
      ENNReal.tendsto_ofReal ((tendsto_iterationScale_zero ht ht1).const_mul (epsilon/4))
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hZero
    (Eventually.of_forall fun _ => bot_le) hBound

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.full_original_norm_tail
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.full_original_norm_convergence
