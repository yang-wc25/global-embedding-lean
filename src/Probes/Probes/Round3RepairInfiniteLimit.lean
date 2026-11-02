import Probes.Round3RepairInfiniteBlocks
import Smoothing.Round3RepairBlockMetricLimit

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
local instance round3RepairInfiniteLimitChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairInfiniteLimitIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M
variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}
  (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)











/-- The terminal assertion names the actual finite oscillatory block sums.
Thus the metric, smoothness and original C2 reserves refer to one map. -/
def Round3RepairConstructedLimitConclusion [CompactSpace M]
    {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
    {budget epsilon eta t : ℝ} {ht : 0 < t} {ht1 : t < 1}
    {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
    (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial) : Prop :=
    let u := fun r => (run.block r).increment packet
    let Fstar := fun z => initial.map z+∑' r, u r z
    (∀ z, Summable (fun r => u r z)) ∧
    ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ Fstar ∧
    (∀ p, inducedMetric (I := IT) (fun x => Fstar (p,x)) = packet.metric p) ∧
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
      (fun z => Fstar z-initial.map z))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples < ENNReal.ofReal (epsilon/4) ∧
    packet.mapDistance Fstar ≠ ⊤ ∧ (packet.mapDistance Fstar).toReal < epsilon/2

/-- Least finite waits make every block advance.  The actual finite sum in
each block has the required growing-order budget; consequently those same
maps have one globally smooth exact-metric limit. -/
theorem round3_repair_constructed_infinite_blocks_metric_limit [CompactSpace M]
    (hK : Data.parameterSet = univ)
    {cost : ℕ → Round3RepairPrimitiveCosts} {Cs : ℕ → ℕ → ℝ} {sigma : ℕ → ℝ}
    {budget epsilon eta t : ℝ} (heps : 0 < epsilon) {ht : 0 < t} {ht1 : t < 1}
    {initial : Round3RepairClosedState packet budget epsilon eta 10 t}
    (hSmall : ∀ r, sigma r ≤ (1/2 : ℝ)^5)
    (hDisp : ∀ r, sigma r ≤ epsilon/(8*((cost r).Cmap ((10+r)/2)+1)))
    (hTheta : ∀ r, sigma r < (cost r).Theta^10)
    (run : Round3RepairInfiniteBlocks (Tr := Tr) (Λ := Λ) (Β := Β) (SubSecondary := SubSecondary)
      packet cost Cs sigma budget epsilon eta t ht ht1 initial) :
    Round3RepairConstructedLimitConclusion packet run := by
  let u := fun r => (run.block r).increment packet
  let Fstar := fun z => initial.map z+∑' r, u r z
  have hIndex (r : ℕ) : r ≤ (run.entry r).index := by
    induction r with
    | zero => omega
    | succ r ih => rw [run.next_index r]; omega
  have hScale (r : ℕ) : iterationScale t (run.entry r).index ≤ iterationScale t r := by
    apply Real.rpow_le_rpow_of_exponent_ge ht ht1.le
    exact pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 6/5) (hIndex r)
  have hActual (r : ℕ) := (run.block r).displacement_budget packet heps
    ((run.entry r).admissible.trans (hSmall r)) ((run.entry r).admissible.trans (hDisp r))
    ((run.entry r).admissible.trans_lt (hTheta r))
  have hu (r : ℕ) : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (u r) := (hActual r).1
  have hUpdate (r : ℕ) : (run.entry (r+1)).state.map = fun z => (run.entry r).state.map z+u r z :=
    (run.next_map r).trans ((run.block r).next_map_eq_increment packet)
  have hBound (r : ℕ) : paperAtlasCj ((10+r)/2)
      (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (u r))
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples ≤
        ENNReal.ofReal ((epsilon/4)*iterationScale t r) :=
    (hActual r).2.trans (ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left (hScale r) (by positivity)))
  have hStage : Tendsto (fun r : ℕ => 10+r) atTop atTop := by
    simpa only [Nat.add_comm] using tendsto_add_atTop_nat 10
  have htSmall : t ≤ (1/2 : ℝ)^5 := by
    have h := (run.entry 0).admissible.trans (hSmall 0)
    simpa only [run.initial_index,iterationScale_zero] using h
  have hResult := round3_repair_block_endpoints_metric_limit packet hK budget epsilon eta t (epsilon/4)
    ht htSmall (by positivity) (fun r => 10+r) hStage (fun r => Nat.le_add_right 10 r)
    (fun r => iterationScale t (run.entry r).index) (fun r => iterationScale_pos ht _) hScale
    (fun r => (run.entry r).state) u hu hUpdate hBound
  have hResult' :
      (∀ z, Summable (fun r => u r z)) ∧
      ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ Fstar ∧
      (∀ p, inducedMetric (I := IT) (fun x => Fstar (p,x)) = packet.metric p) ∧
      paperAtlasCj 2 (incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
        (fun z => Fstar z-initial.map z))
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart) packet.closedSamples < ENNReal.ofReal (epsilon/4) := by
    simpa only [run.initial_map] using hResult
  let f := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart
    (fun z => initial.map z-packet.referenceMap z)
  let v := incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => Fstar z-initial.map z)
  let O := incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hf := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB _ (initial.smooth.sub packet.referenceMap_smooth)
  have hv := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB _ (hResult'.2.1.sub initial.smooth)
  have hvFin : paperAtlasCj 2 v O packet.closedSamples ≠ ⊤ :=
    ne_top_of_lt (hResult'.2.2.2.trans ENNReal.ofReal_lt_top)
  have hvReal : (paperAtlasCj 2 v O packet.closedSamples).toReal < epsilon/4 := by
    have h := (ENNReal.toReal_lt_toReal hvFin ENNReal.ofReal_ne_top).mpr hResult'.2.2.2
    simpa only [ENNReal.toReal_ofReal (show 0 ≤ epsilon/4 by positivity)] using h
  have hadd := parameterRound2_paperAtlasCj_add_le 2 f v O packet.closedSamples
    (parameterRound2_originalDifferentiation_open Data.atlas packet.parameterFamily.chart)
    (fun _ _ hy => hy.1) hf hv initial.mapDistance_finite hvFin
  have hEq : (fun i y => f i y+v i y) =
      incrementsOriginalMapCoordinates Data.atlas packet.parameterFamily.chart (fun z => Fstar z-packet.referenceMap z) := by
    funext i y a
    simp only [f,v,incrementsOriginalMapCoordinates,map_add,map_sub,Pi.add_apply,Pi.sub_apply]
    ring
  rw [hEq] at hadd
  have hFin : packet.mapDistance Fstar ≠ ⊤ :=
    ne_top_of_le_ne_top (ENNReal.add_ne_top.mpr ⟨initial.mapDistance_finite,hvFin⟩) hadd
  have hReal := ENNReal.toReal_mono (ENNReal.add_ne_top.mpr ⟨initial.mapDistance_finite,hvFin⟩) hadd
  rw [ENNReal.toReal_add initial.mapDistance_finite hvFin] at hReal
  have hOld : (packet.mapDistance initial.map).toReal ≤ epsilon/4 := by
    have h := initial.map_close
    nlinarith [mul_nonneg heps.le ht.le]
  refine ⟨hResult'.1,hResult'.2.1,hResult'.2.2.1,hResult'.2.2.2,hFin,?_⟩
  change (packet.mapDistance Fstar).toReal ≤ (packet.mapDistance initial.map).toReal+
    (paperAtlasCj 2 v O packet.closedSamples).toReal at hReal
  linarith only [hReal,hOld,hvReal]

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_constructed_infinite_blocks_metric_limit
