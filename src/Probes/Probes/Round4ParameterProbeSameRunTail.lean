import Probes.Round3RepairFullJets
import Probes.Round4ParameterProbeActualIncrement
import Probes.Round4ParameterProbeOriginalSum

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
local instance round4ParameterProbeSameRunTailChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterProbeSameRunTailIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
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

/-- The same actual infinite sum has the precise original total-order
bounds, obtained from its primitive U and the single three-order entrance. -/
theorem probe_original_tail_order
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (a : ℕ) (ha : 1 ≤ a) (ha3 : a ≤ 3) :
    paperAtlasCj a
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => ∑' j, run.increment packet j z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
      ENNReal.ofReal (2*round4ParameterProbeTailConstant cost *
        t^((10 : ℝ)+(6/5 : ℝ)*(1-(a : ℝ)))) := by
  have htSmall : t ≤ (1/2 : ℝ)^5 := by
    have h := (run.entry 0).admissible.trans (hSmall 0)
    simpa only [run.initial_index,iterationScale_zero] using h
  have hp : (1 : ℝ) ≤ 10+(6/5 : ℝ)*(1-(a : ℝ)) := by
    have ha3' : (a : ℝ) ≤ 3 := by exact_mod_cast ha3
    linarith
  have hActual := run.full_increment_control packet heps hDisp hTheta
  have h := round4ParameterProbe_closed_original_sum_fixed_order packet hK
    (run.increment packet) (run.stage packet) (fun j => (hActual j).1)
    (run.full_stage_tendsto packet)
    (fun j => (show 4 ≤ 10 by norm_num).trans (run.full_stage_ge_ten packet j))
    a t (epsilon/8) ht htSmall (by positivity) (fun j => (hActual j).2)
    (round4ParameterProbeTailConstant cost) (10+(6/5 : ℝ)*(1-(a : ℝ)))
    (round4ParameterProbeTailConstant_pos cost).le (by linarith)
    (run.probe_increment_original_order packet hTheta hCap a ha ha3)
  exact h.trans (ENNReal.ofReal_le_ofReal ((mul_le_mul_of_nonneg_left
    (tsum_iterationScale_power_le_twice_of_small ht htSmall hp)
    (round4ParameterProbeTailConstant_pos cost).le).trans_eq (by ring)))

/-- Equation (8.4), in the original atlas maximum, for the actual repair
started at t₁=t^(6/5). The subtraction uses the given initial map, which
can be the genuine G₁ once its closed-state producer has been supplied. -/
theorem probe_original_tail_84
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ)) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    let tail := fun z => Fstar z-initial.map z
    paperAtlasCj 3 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (2*round4ParameterProbeTailConstant cost*s^(228/25 : ℝ)) ∧
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (2*round4ParameterProbeTailConstant cost*s^(264/25 : ℝ)) ∧
    paperAtlasCj 1 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal (2*round4ParameterProbeTailConstant cost*s^(12 : ℝ)) := by
  have h3 := run.probe_original_tail_order packet hK heps hSmall hDisp hTheta hCap 3 (by omega) (by omega)
  have h2 := run.probe_original_tail_order packet hK heps hSmall hDisp hTheta hCap 2 (by omega) (by omega)
  have h1 := run.probe_original_tail_order packet hK heps hSmall hDisp hTheta hCap 1 (by omega) (by omega)
  conv at h3 => rhs; rw [hstart,← Real.rpow_mul hs.le]
  conv at h2 => rhs; rw [hstart,← Real.rpow_mul hs.le]
  conv at h1 => rhs; rw [hstart,← Real.rpow_mul hs.le]
  norm_num at h3 h2 h1
  have h12 : s^(12 : ℝ) = s^(12 : ℕ) := by norm_num
  simpa only [add_sub_cancel_left,h12] using And.intro h3 (And.intro h2 h1)

/-- The literal mixed source/parameter words in (8.4), on the same original
closed samples and same exact metric limit. Values and parameter order zero
are retained, so the last estimate also bounds the actual first response. -/
theorem probe_mixed_tail_84
    (hK : Data.parameterSet = univ) (heps : 0 < epsilon)
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (hCap : ∀ r, sigma r ≤ round4ParameterProbeTailCap cost r)
    (s : ℝ) (hs : 0 < s) (hstart : t=s^(6/5 : ℝ)) :
    let Fstar := fun z => initial.map z+∑' j, run.increment packet j z
    let tail := fun z => Fstar z-initial.map z
    (⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) 2 1
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) ≤
        ENNReal.ofReal (2*round4ParameterProbeTailConstant cost*s^(228/25 : ℝ)) ∧
    (⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) 1 1
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) ≤
        ENNReal.ofReal (2*round4ParameterProbeTailConstant cost*s^(264/25 : ℝ)) ∧
    (⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) 0 1
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) ≤
        ENNReal.ofReal (2*round4ParameterProbeTailConstant cost*s^(12 : ℝ)) := by
  intro Fstar tail
  have hOriginal := run.probe_original_tail_84 packet hK heps hSmall hDisp hTheta hCap s hs hstart
  have hFull := run.full_metric_limit packet hK heps hSmall hDisp hTheta
  have hSmooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ tail := hFull.2.1.sub initial.smooth
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hCompare (a b : ℕ) :
      (⨆ i, paperMixedCoordinateCj (nx := m+1) (np := d) a b
        (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) (packet.closedSamples i)) ≤
      paperAtlasCj (a+b) (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples := by
    apply iSup_le
    intro i
    exact (paperMixedCoordinateCj_le_total a b _ _ _
      (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart i)
      (fun _ hy => hy.1)
      (parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
        packet.domain.atlas_smooth hB tail hSmooth i)).trans
        (le_iSup (fun idx => paperCoordinateCj (a+b)
          (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart tail idx)
          (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart idx) (packet.closedSamples idx)) i)
  exact ⟨(hCompare 2 1).trans hOriginal.1,
    (hCompare 1 1).trans hOriginal.2.1,(hCompare 0 1).trans hOriginal.2.2⟩

end Round3RepairInfiniteBlocks
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.probe_original_tail_order
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.probe_original_tail_84
#print axioms GlobalEmbedding.Continuation.Round3RepairInfiniteBlocks.probe_mixed_tail_84
