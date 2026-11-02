import Smoothing.Round3RepairOriginalSmoothingStageData
import Smoothing.Round4RepairSmoothingProfiles
import Smoothing.ParameterRound2OriginalSmoothedStageProfiles

/-! The SAME signed-kernel smoother supplies the actual original stage
background, target, and every original given-input profile. The only packet
budget left outside the smoother is the actual given cutoff/normal/linear,
phase differential and original chart-transition data at fixed scale one.
No smoothed-map or smoothed-target derivative estimate is assumed. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
local instance round4ParameterStageDataChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance round4ParameterStageDataIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round4Parameter_actual_stage_data_named_profiles
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    let Cmap := fun j => round4PreparedPairConstant n d radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
    let Ctarget := Cmap
    (∀ j, 0 ≤ Cmap j) ∧ (∀ j, 0 ≤ Ctarget j) ∧ ∀
    (Data : IncrementsOriginalNativeData n d N M P) (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W := incrementsOriginalParameterRegion Data
    ∃ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W,
    H.val = Data.H ∧
    (∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W stage.samples_compact
      (fun _ _ hy => hy.1) stage.ell j H ≤ Ctarget j*budget+(j+1)*reference j) ∧
    (∀ j, actualOriginalGivenInputProfile Data j stage.ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j stage.ell).toReal ≤
        max (Cmap j*budget) (max (Ctarget j*budget+(j+1)*reference j) (givenPacket j))) := by
  intro Cmap Ctarget
  obtain ⟨hCmap,hCtarget,hprod⟩ := round4_actual_original_smoothed_stage_profiles
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨hCmap,hCtarget,?_⟩
  intro Data budget reference givenPacket stage
  exact hprod Data stage.parameterFamily stage.chart_eq stage.atlas_smooth stage.parameter_smooth
    stage.sourcePreparation stage.parameterPreparation stage.buffer stage.Omega stage.Q
    stage.source_compact stage.parameter_compact stage.source_target stage.parameter_target
    stage.source_sampling stage.parameter_sampling stage.samples_compact
    stage.ell stage.t stage.ell_pos stage.ell_le_t stage.t_le_one stage.oldMap stage.referenceMap
    stage.oldMap_smooth stage.referenceMap_smooth reference stage.reference_bound stage.metric
    stage.metric_symmetric stage.metric_smooth stage.delta stage.deltaNext stage.reserve_ratio budget
    stage.old_pair_budget stage.map_eq stage.target_eq givenPacket stage.given_finite stage.given_bound

#print axioms round4Parameter_actual_stage_data_named_profiles
end GlobalEmbedding.Continuation
