import Smoothing.Round3RepairOriginalSmoothingStageData
import Smoothing.ParameterRound2RepairIdentity
import Probes.ActualIncrementOriginalOpenSlice

/-! The literal smoothed map in an actual repair stage is jointly smooth.
The identity-coordinate open slice agrees with that same map throughout the
original parameter region, so its joint regularity is produced internally.
-/

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
local instance round3RepairStageSmoothChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance round3RepairStageSmoothIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

theorem round3_repair_stage_smoothed_map_contMDiff
    (Data : IncrementsOriginalNativeData n d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (q : ℕ)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius q
      budget reference givenPacket) :
    ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ Data.F := by
  let mu := (volume : Measure (Ep × D))
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hK := fixedSmoothingKernel_spec mu radius hradius q
  obtain ⟨Bc,hBc,hprep⟩ := exists_uniform_local_product_smoothing_providers
    (Es := D) («Ep» := Ep) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp
  obtain ⟨W,hW,hKW,hchi,hpart,hsupp,hD,hw,ht⟩ := hprep
    Data.parameterCount Data.atlas stage.parameterFamily stage.atlas_smooth stage.parameter_smooth
    Data.parameterSet stage.sourcePreparation stage.parameterPreparation
  have hcoords := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas stage.parameterFamily.chart
    stage.atlas_smooth stage.parameter_smooth stage.oldMap stage.oldMap_smooth
  rw [stage.map_eq]
  exact parameterLocalMapSmoothing_contMDiff (parameterLocalProductFamily Data.atlas stage.parameterFamily)
    (parameterLocalProductFamily_chart_mem Data.atlas stage.parameterFamily
      stage.atlas_smooth stage.parameter_smooth) mu hK.1 hK.2.1 hK.2.2.1
    stage.buffer stage.ell_pos.le (stage.ell_le_t.trans stage.t_le_one)
    _ hchi hsupp stage.oldMap (parameterLocalMapInput_contDiffOn _ _ _ hcoords)

theorem round3_repair_stage_open_slice_contMDiffOn
    [BoundarylessManifold 𝓙 M]
    (Data : IncrementsOriginalNativeData n d N M Ep)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (q : ℕ)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius q
      budget reference givenPacket)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (hId : Data.parameterChart i.2 = OpenPartialHomeomorph.refl Ep) :
    ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,V) ∞
      (fun z : Ep × M => actualOriginalOpenParameterSlice Data i z.1 z.2)
      (incrementsOriginalParameterRegion Data) := by
  have hF := round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0
    Ds Dp radius hradius q budget reference givenPacket stage
  rw [modelWithCornersSelf_prod] at hF
  apply hF.contMDiffOn.congr
  intro z hz
  have hp : (Data.parameterChart i.2).symm z.1 ∈ Data.parameterOpen := by
    simpa only [hId,OpenPartialHomeomorph.refl_symm,OpenPartialHomeomorph.refl_apply,id_eq] using hz.1
  rw [actualOriginalOpenParameterSlice_eq Data i z.1 hp]
  simp only [actualOriginalParameterSlice,hId,OpenPartialHomeomorph.refl_symm,
    OpenPartialHomeomorph.refl_apply,id_eq]

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_repair_stage_smoothed_map_contMDiff
#print axioms GlobalEmbedding.Continuation.round3_repair_stage_open_slice_contMDiffOn
