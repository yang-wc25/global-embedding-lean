import Smoothing.Round3RepairInitialState
import Smoothing.Round3RepairClosedTargetData
import Smoothing.Round3OuterRepairTargetProfiles

/-! Actual closed-domain repair states.  The defect is always computed from
the same current map and the prescribed metric.  The map reserve includes a
remaining-scale envelope, so one actual small increment preserves the C2
entrance without a fictitious unchanged distance bound. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
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
local instance round3RepairTargetBeforeMetricChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairTargetBeforeMetricIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

variable {Data : IncrementsOriginalNativeData (m+1) d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

namespace Round3RepairFixedSmoothingPacket
variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)

/-- The actual same SF/SH target supplies its global germ and all numerical
mean-input bounds on the unchanged closed Ω/Q samples. No derivative bound,
regularity or symmetry of the smoothed fields is a premise. -/
theorem closed_actual_target_data_before_metric [CompactSpace M]
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hK : Data.parameterSet = univ) (r : ℕ) :
    ∃ Ctarget : ℕ → ℝ, (∀ j, 0 ≤ Ctarget j) ∧
    ∀ (metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x))
      (hSym : ∀ p x, (metric p x).IsSymm)
      (hSmooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas
        packet.parameterFamily.chart metric i)
        (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i)),
    let changed := packet.withMetric metric hSym hSmooth
    ∀ (budget : ℝ) (state : Round3RepairCurrentSmoothingState changed r budget),
      ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (state.smoothedMap changed) ∧
      (∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => state.smoothedMap changed (p,x))) ∧
      ∃ H : parameterRound2_originalTensorGermSpace Data.atlas packet.parameterFamily.chart packet.closedSamples univ,
        H.val=state.computedTarget changed ∧
        ∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas packet.parameterFamily.chart packet.closedSamples univ
          packet.closedSamples_compact (fun _ _ hy => hy.1) state.ell j H ≤
          Ctarget j*budget+(j+1)*packet.closedReferenceProfile j := by
  obtain ⟨Ctarget,hCtarget,hTarget⟩ := round3Outer_exists_uniform_actual_repair_target_slow_profiles
    (n := m+1) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨Ctarget,hCtarget,?_⟩
  intro metric hSym hSmooth changed budget state
  have hSF := round3_repair_stage_smoothed_map_contMDiff
    (state.computedData changed univ 1) BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
    Ds Dp radius hradius r budget reference givenPacket (state.toStage changed univ 1)
  change ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ (state.smoothedMap changed) at hSF
  have hSlice : ∀ p, ContMDiff IT 𝓘(ℝ,Ey) ∞ (fun x => state.smoothedMap changed (p,x)) := by
    intro p
    rw [modelWithCornersSelf_prod] at hSF
    exact hSF.comp (contMDiff_const.prodMk contMDiff_id)
  have hB : ∀ i, changed.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [changed.chart_eq]
    exact changed.domain.parameter_charts_smooth
  obtain ⟨H,hH,hBound⟩ := hTarget Data.parameterCount Data.atlas changed.parameterFamily
    changed.domain.atlas_smooth hB univ changed.sourcePreparation (changed.closedParameterPreparation hK)
    changed.buffer changed.Omega changed.Q changed.source_compact changed.parameter_compact
    changed.source_target changed.parameter_target changed.source_sampling changed.parameter_sampling
    changed.closedSamples univ changed.closedSamples_compact (fun _ _ hy => hy.1)
    (fun _ _ hy => ⟨hy.1,mem_univ _⟩)
    state.ell state.t state.ell_pos state.ell_le_t state.t_le_one
    state.oldMap changed.referenceMap state.oldMap_smooth changed.referenceMap_smooth
    changed.closedReferenceProfile (fun _ => le_rfl) changed.metric changed.metric_symmetric changed.metric_smooth
    state.delta state.deltaNext state.reserve_ratio budget state.old_pair_budget
  refine ⟨hSF,hSlice,H,?_,hBound⟩
  rw [hH]
  unfold Round3RepairCurrentSmoothingState.computedTarget Round3RepairCurrentSmoothingState.normalizedDefect
  rw [changed.reference_tensor]
  rfl

end Round3RepairFixedSmoothingPacket
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairFixedSmoothingPacket.closed_actual_target_data_before_metric
