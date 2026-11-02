import Smoothing.Round3RepairClosedTargetData
import Smoothing.Round4SpatialRepairTargetProfiles
import Probes.Round4ParameterSpatialDominatedByTotal

/-!
# The unchanged closed repair target with a finite named smoother cost

The actual SF/SH, fixed closed samples and original target germ are exactly
those used by repair. Their target budget now uses the literal spatial-pair cost
whose order-j entry reads the raw cutoff/transition profiles only through
j+2. No estimate of the smoothed fields is added as a premise.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round4ParameterClosedTargetChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round4ParameterClosedTargetIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

namespace Round3RepairCurrentSmoothingState

/-- Existing stronger working states supply the literal spatial budget by
the proved one-way comparison, with finiteness established before toReal. -/
theorem round4_spatial_pair_budget
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    {r : ℕ} {budget : ℝ} (state : Round3RepairCurrentSmoothingState packet r budget) :
    (round4ParameterSpatialPairWeighted Data.atlas packet.parameterFamily state.oldMap
      (state.normalizedDefect packet) r state.t packet.closedSamples).toReal ≤ budget := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hF := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB state.oldMap state.oldMap_smooth
  have hfinite := parameterRound2_original_pair_on_compact_finite Data.atlas packet.parameterFamily
    packet.Omega packet.Q packet.source_compact packet.parameter_compact
    packet.source_target packet.parameter_target state.oldMap hF
    (state.normalizedDefect packet) (state.normalizedDefect_smooth packet) r state.t
  have hle := round4ParameterSpatialPairWeighted_le_total Data.atlas packet.parameterFamily
    state.oldMap (state.normalizedDefect packet) packet.closedSamples (fun _ _ hz => hz.1)
    hF r state.t
  exact (ENNReal.toReal_mono hfinite hle).trans state.old_pair_budget

end Round3RepairCurrentSmoothingState

namespace Round3RepairFixedSmoothingPacket
variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

theorem round4_closed_actual_target_data [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (r : ℕ) :
    let Ctarget := fun j => round4SpatialPairConstant n d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
    (∀ j, 0 ≤ Ctarget j) ∧
    ∀ (budget : ℝ) (state : Round3RepairCurrentSmoothingState packet r budget),
      ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (state.smoothedMap packet) ∧
      (∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => state.smoothedMap packet (p,x))) ∧
      ∃ H : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ,
        H.val=state.computedTarget packet ∧
        ∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
          packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell j H ≤
          Ctarget j*budget+(j+1)*packet.closedReferenceProfile j := by
  intro Ctarget
  obtain ⟨hCtarget,hTarget⟩ := round4_actual_spatial_repair_target_slow_profiles
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨hCtarget,?_⟩
  intro budget state
  have hSF := round3_repair_stage_smoothed_map_contMDiff
    (state.computedData packet univ 1) BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
    Ds Dp radius hradius r budget reference givenPacket (state.toStage packet univ 1)
  change ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (state.smoothedMap packet) at hSF
  have hSlice : ∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => state.smoothedMap packet (p,x)) := by
    intro p
    rw [modelWithCornersSelf_prod] at hSF
    exact hSF.comp (contMDiff_const.prodMk contMDiff_id)
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  obtain ⟨H,hH,hBound⟩ := hTarget Data.parameterCount Data.atlas packet.parameterFamily
    packet.domain.atlas_smooth hB packet.sourcePreparation (packet.closedParameterPreparation hK)
    packet.buffer packet.Omega packet.Q packet.source_compact packet.parameter_compact
    packet.source_target packet.parameter_target packet.source_sampling packet.parameter_sampling
    packet.closedSamples univ packet.closedSamples_compact (fun _ _ hy => hy.1)
    (fun _ => Subset.rfl)
    state.ell state.t state.ell_pos state.ell_le_t state.t_le_one
    state.oldMap packet.referenceMap state.oldMap_smooth packet.referenceMap_smooth
    packet.closedReferenceProfile (fun _ => le_rfl) packet.metric packet.metric_symmetric packet.metric_smooth
    state.delta state.deltaNext state.reserve_ratio budget (state.round4_spatial_pair_budget packet)
  refine ⟨hSF,hSlice,H,?_,hBound⟩
  rw [hH]
  unfold Round3RepairCurrentSmoothingState.computedTarget Round3RepairCurrentSmoothingState.normalizedDefect
  rw [packet.reference_tensor]
  rfl

end Round3RepairFixedSmoothingPacket
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairCurrentSmoothingState.round4_spatial_pair_budget
#print axioms GlobalEmbedding.Continuation.Round3RepairFixedSmoothingPacket.round4_closed_actual_target_data
