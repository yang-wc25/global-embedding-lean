import Smoothing.Round3OuterShiftedSpatialProfiles
import Smoothing.Round3OuterLocalSetPair
import Smoothing.Round3RepairStageSmoothMap

/-! The actual signed-kernel stage map supplies every joint slow profile
of its spatial first derivative and Hessian in a fixed reference chart.
The constants are selected before the current map, the stage scale, and
the literal SF/SH pair.  Only the original old C2/C0 pair budget is used;
no compact maximum of the current smoothed map is selected afterwards.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × Es
local instance round3StageSpatialChartedSpace : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3StageSpatialIsManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

theorem round3_exists_uniform_actual_stage_first_hessian_profiles
    (BS0 TS0 BP0 TP0 T : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    ∃ C : ℕ → ℝ, (∀ j, 0 ≤ C j) ∧ ∀
    (Data : IncrementsOriginalNativeData n d N M P)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    ∀ (j : ℕ) (i : Fin Data.atlas.count × Fin Data.parameterCount)
      (e : Ep → OpenPartialHomeomorph M Es) (O Z : Set X),
    IsOpen O → Z ⊆ O →
    ContDiffOn ℝ ∞ (round3OriginalAdaptedTransition Data.atlas i.1 e) O →
    (∀ z ∈ O, (e z.1).symm z.2 ∈ (Data.atlas.chart i.1).source) →
    (∀ z ∈ O, z.1 ∈ (Data.parameterChart i.2).target) →
    (∀ z ∈ Z, parameterTensorModelEquiv n d
      (round3OriginalAdaptedTransition Data.atlas i.1 e z) ∈ S i) →
    (∀ l, 1 ≤ l → l ≤ j+2 → ∀ z ∈ Z,
      ‖iteratedFDeriv ℝ l (round3OriginalAdaptedTransition Data.atlas i.1 e) z‖ ≤ T l) →
    let f := fun w : X => Data.F ((Data.parameterChart i.2).symm w.1,(e w.1).symm w.2)
    (ContDiffOn ℝ ∞ (fun w : X => fderiv ℝ (fun x => f (w.1,x)) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ Z, stage.ell^k*‖iteratedFDeriv ℝ k
        (fun w : X => fderiv ℝ (fun x => f (w.1,x)) w.2) z‖ ≤ C j*budget) ∧
    (ContDiffOn ℝ ∞ (fun w : X => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) O ∧
      ∀ k ≤ j, ∀ z ∈ Z, stage.ell^k*‖iteratedFDeriv ℝ k
        (fun w : X => fderiv ℝ (fderiv ℝ (fun x => f (w.1,x))) w.2) z‖ ≤ C j*budget) := by
  have hm (j : ℕ) := round3Outer_exists_uniform_parameterRound2_local_set_pair_smoothing
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j r
  let Cm : ℕ → ℝ := fun j => Classical.choose (hm j)
  have hCm : ∀ j, 0 ≤ Cm j := fun j => (Classical.choose_spec (hm j)).1
  let C : ℕ → ℝ := fun j => round3OriginalShiftedAdaptedCost n d N T j*Cm j
  refine ⟨C,fun j => mul_nonneg (round3OriginalShiftedAdaptedCost_nonneg n d N T hT j) (hCm j),?_⟩
  intro Data budget reference givenPacket stage S j i e O Z hO hZO hTransition hSource hParameter hSample hChartJets
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans stage.old_pair_budget
  have hOld := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas stage.parameterFamily.chart
    stage.atlas_smooth stage.parameter_smooth stage.oldMap stage.oldMap_smooth
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn Data.atlas
    stage.parameterFamily.chart stage.atlas_smooth stage.parameter_smooth stage.oldMap stage.oldMap_smooth
    stage.metric stage.metric_smooth stage.delta
  have hSO : ∀ a, S a ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart a :=
    fun _ _ hy => hy.1
  have hSouter : ∀ a, S a ⊆ round3OuterOriginalEvaluation Data.atlas stage.parameterFamily Data.parameterSet a := by
    intro a y hy
    refine ⟨?_,?_⟩
    · simpa only [stage.chart_eq] using hy.1
    · change (incrementsOriginalJointPoint Data.atlas stage.parameterFamily.chart a y).1 ∈ Data.parameterSet
      simpa only [stage.chart_eq] using hy.2.2.2
  have hpair := (Classical.choose_spec (hm j)).2 Data.parameterCount Data.atlas stage.parameterFamily
    stage.atlas_smooth stage.parameter_smooth Data.parameterSet stage.sourcePreparation stage.parameterPreparation
    stage.buffer stage.Omega stage.Q stage.source_compact stage.parameter_compact stage.source_target
    stage.parameter_target stage.source_sampling stage.parameter_sampling S hSouter
    stage.ell stage.ell stage.t stage.ell_pos le_rfl stage.ell_le_t stage.t_le_one
    stage.oldMap hOld _ hHold budget stage.old_pair_budget
  have hmle : paperAtlasWeighted 2 j stage.ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≤
      parameterLocalOriginalTotalPairWeighted Data.atlas stage.parameterFamily Data.F
        (tensorLocalParameterSmoothing Data.atlas stage.parameterFamily stage.atlas_smooth
          (volume : Measure X) (fixedSmoothingKernel (volume : Measure X) radius hradius r) stage.ell
          (parameterLocalProductCutoff Data.atlas stage.parameterFamily
            (squareNormalizedCutoff stage.sourcePreparation.raw)
            (tensorLocalNormalizedCutoff stage.parameterPreparation.raw))
          (fun p x => (stage.delta^2)⁻¹ • (stage.metric p x -
            inducedMetric (I := 𝓘(ℝ,Es)) (fun y => stage.oldMap (p,y)) x))) j stage.ell S := by
    rw [← stage.chart_eq]
    exact le_add_right le_rfl
  dsimp only at hpair
  rw [← stage.map_eq] at hpair
  have hfin := ne_top_of_le_ne_top hpair.2.2.2.2.1 hmle
  have hbound := (ENNReal.toReal_mono hpair.2.2.2.2.1 hmle).trans hpair.2.2.2.2.2
  have hSF := round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
    hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage
  have hcoords : ∀ a, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F a)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart a) := by
    rw [← stage.chart_eq]
    exact parameterRound2_originalMapCoordinates_contDiffOn Data.atlas stage.parameterFamily.chart
      stage.atlas_smooth stage.parameter_smooth Data.F hSF
  have h := round3_original_fixed_chart_first_hessian_profiles T hT Data.atlas Data.parameterChart
    Data.F S hSO hcoords j stage.ell stage.ell_pos (stage.ell_le_t.trans stage.t_le_one)
    hfin (Cm j*budget) (mul_nonneg (hCm j) hbudget0) hbound i e O Z hO hZO
    hTransition hSource hParameter hSample hChartJets
  simpa only [C,mul_assoc] using h

#print axioms round3_exists_uniform_actual_stage_first_hessian_profiles
end GlobalEmbedding.Continuation
