import Smoothing.Round3RepairStageSmoothMap
import Smoothing.ParameterRound2RepairRegularity

/-! The literal stage supplies actual target regularity and both generated
smooth fields in the original input record.  Reference phases, cutoffs, and
the actual rebound normal retain their own genuine joint smoothness domains. -/
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
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "IT" => 𝓘(ℝ,Es)
local instance round3RepairTargetChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairTargetIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

theorem round3_repair_stage_target_coordinates_smooth
    (Data : IncrementsOriginalNativeData n d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (q : ℕ)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius q
      budget reference givenPacket) :
    ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H i)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart i) := by
  let mu := (volume : Measure (Ep × Es))
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hK := fixedSmoothingKernel_spec mu radius hradius q
  obtain ⟨Bc,hBc,hprep⟩ := exists_uniform_local_product_smoothing_providers
    («Es» := Es) («Ep» := Ep) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
  obtain ⟨W,hW,hKW,hchi,hpart,hsupp,hD,hw,ht⟩ := hprep
    Data.parameterCount Data.atlas stage.parameterFamily stage.atlas_smooth stage.parameter_smooth
    Data.parameterSet stage.sourcePreparation stage.parameterPreparation
  let Hold := fun p x => (stage.delta^2)⁻¹ •
    (stage.metric p x-inducedMetric (I := IT) (fun y => stage.oldMap (p,y)) x)
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn Data.atlas
    stage.parameterFamily.chart stage.atlas_smooth stage.parameter_smooth stage.oldMap stage.oldMap_smooth
    stage.metric stage.metric_smooth stage.delta
  have hSH := tensorLocalParameterSmoothing_original_contDiffOn Data.atlas stage.parameterFamily
    stage.atlas_smooth stage.parameter_smooth mu hK.1 hK.2.1 hK.2.2.1
    stage.buffer stage.ell_pos.le (stage.ell_le_t.trans stage.t_le_one) _ hchi hsupp Hold hHold
  have hRef := parameterRound2_inducedMetric_originalCoordinates_contDiffOn Data.atlas
    stage.parameterFamily.chart stage.atlas_smooth stage.parameter_smooth stage.referenceMap stage.referenceMap_smooth
  intro i
  rw [stage.target_eq,← stage.chart_eq]
  exact (hSH i).sub ((hRef i).const_smul ((stage.deltaNext/stage.delta)^2))

/-- Original input smoothness for the generated F/H.  Their smoothness is
proved from the same actual smoother, rather than required again upstream. -/
theorem round3_repair_stage_original_smooth_inputs
    [BoundarylessManifold IT M]
    (Data : IncrementsOriginalNativeData n d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (q : ℕ)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius q
      budget reference givenPacket)
    (hPhase : ∀ ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,ℝ) ∞ (Data.phase ν)
      (Data.primaryDomain ν ∩ incrementsOriginalParameterRegion Data))
    (hCutoff : ∀ ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,ℝ) ∞ (Data.cutoff ν)
      (Data.primaryDomain ν ∩ incrementsOriginalParameterRegion Data))
    (hNormal : ∀ ν, ContMDiffOn ((𝓘(ℝ,Ep)).prod IT) 𝓘(ℝ,Ey) ∞ (Data.freeNormal ν)
      (Data.primaryDomain ν ∩ incrementsOriginalParameterRegion Data)) :
    IncrementsOriginalSmoothInputs Data := by
  have hF := round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
    hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q budget reference givenPacket stage
  have hH := round3_repair_stage_target_coordinates_smooth Data BS0 TS0 BP0 TP0
    hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius q budget reference givenPacket stage
  rw [modelWithCornersSelf_prod] at hF
  exact ⟨hF.contMDiffOn,fun i => (hH i).mono inter_subset_left,hPhase,hCutoff,hNormal⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_repair_stage_target_coordinates_smooth
#print axioms GlobalEmbedding.Continuation.round3_repair_stage_original_smooth_inputs
