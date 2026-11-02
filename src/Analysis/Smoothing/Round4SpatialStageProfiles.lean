import Smoothing.Round4SpatialAdaptedProfiles
import Probes.Round4ParameterSpatialDominatedByTotal
import Smoothing.Round4SpatialPreparedGain
import Smoothing.Round3RepairStageSmoothMap

/-! The actual existing repair stage consumes the literal spatial (6.4)
smoother. Its old total working budget supplies the genuine spatial budget
through the proved constant-one inequality; no equality of the two norms is
used. The closed parameter condition is explicit. The actual adapted first
and Hessian fields are then obtained through the true triangular source
coordinate change, without an extra inverse power of ell.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
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
private local instance round4LiteralSpatialStageChartedSpace : ChartedSpace X (P × M) :=
  prodChartedSpace Ep P Es M
private local instance round4LiteralSpatialStageIsManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,Es)) (n := ∞) P M

/-- The concrete adapted-coordinate first/Hessian profile of the actual
signed-kernel stage map. The old pair budget is multiplied only afterwards. -/
def round4SpatialStageProfile (n d N : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (BS0 TS0 BP0 TP0 T : ℕ → ℝ) (Ds Dp r j : ℕ) : ℝ :=
  round4OriginalSpatialAdaptedCost n d N T j *
    round4SpatialPairConstant n d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j r

theorem round4SpatialStageAdaptedCost_congr_prefix (n d N j : ℕ)
    {T₁ T₂ : ℕ → ℝ} (hT : ∀ a ≤ j+2, T₁ a = T₂ a) :
    round4OriginalSpatialAdaptedCost n d N T₁ j =
      round4OriginalSpatialAdaptedCost n d N T₂ j := by
  exact round4OriginalSpatialAdaptedCost_congr_prefix n d N j hT

/-- All five raw/reference geometry profiles are read only through j+2,
independently of the fixed kernel moment order. -/
theorem round4SpatialStageProfile_congr_prefix
    (n d N : ℕ) (radius : ℝ) (hradius : 0 < radius) (Ds Dp r j : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ T₁ T₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ j+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j+2, TP₁ a = TP₂ a)
    (hT : ∀ a ≤ j+2, T₁ a = T₂ a) :
    round4SpatialStageProfile n d N radius hradius BS₁ TS₁ BP₁ TP₁ T₁ Ds Dp r j =
      round4SpatialStageProfile n d N radius hradius BS₂ TS₂ BP₂ TP₂ T₂ Ds Dp r j := by
  unfold round4SpatialStageProfile
  rw [round4SpatialStageAdaptedCost_congr_prefix n d N j hT,
    round4SpatialPairConstant_congr_prefix n d N radius hradius Ds Dp j r hBS hTS hBP hTP]

theorem round4_actual_spatial_stage_first_hessian_profiles
    (BS0 TS0 BP0 TP0 T : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j)
    (hT : ∀ j, 0 ≤ T j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    let C := round4SpatialStageProfile n d N radius hradius BS0 TS0 BP0 TP0 T Ds Dp r
    (∀ j, 0 ≤ C j) ∧ ∀
    (Data : IncrementsOriginalNativeData n d N M P)
    (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : Round3RepairOriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp
      radius hradius r budget reference givenPacket),
    Data.parameterSet = univ →
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
  have hm (j : ℕ) := round4_actual_spatial_prepared_gain_on_targets
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius j r
  let Cm : ℕ → ℝ := fun j => round4SpatialPairConstant n d N radius hradius BS0 TS0 BP0 TP0 Ds Dp j r
  have hCm : ∀ j, 0 ≤ Cm j := fun j => (hm j).1
  let C : ℕ → ℝ := fun j => round4OriginalSpatialAdaptedCost n d N T j*Cm j
  refine ⟨fun j => mul_nonneg (round4OriginalSpatialAdaptedCost_nonneg n d N T hT j) (hCm j),?_⟩
  intro Data budget reference givenPacket stage hK S j i e O Z hO hZO hTransition hSource hParameter hSample hChartJets
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans stage.old_pair_budget
  have hOld := parameterRound2_originalMapCoordinates_contDiffOn Data.atlas stage.parameterFamily.chart
    stage.atlas_smooth stage.parameter_smooth stage.oldMap stage.oldMap_smooth
  have hHold := parameterRound2_normalizedDefect_originalCoordinates_contDiffOn Data.atlas
    stage.parameterFamily.chart stage.atlas_smooth stage.parameter_smooth stage.oldMap stage.oldMap_smooth
    stage.metric stage.metric_smooth stage.delta
  have hSO : ∀ a, S a ⊆ incrementsOriginalDifferentiation Data.atlas Data.parameterChart a :=
    fun _ _ hy => hy.1
  let RPclosed : TensorLocalRawPreparation stage.parameterFamily univ BP0 TP0 Dp :=
    { raw := stage.parameterPreparation.raw
      smooth := stage.parameterPreparation.smooth
      plateau_on := fun p _ => stage.parameterPreparation.plateau_on p (by rw [hK]; trivial)
      inner_support := stage.parameterPreparation.inner_support
      enlarged := stage.parameterPreparation.enlarged
      enlarged_support := stage.parameterPreparation.enlarged_support
      degree := stage.parameterPreparation.degree
      own_jets := stage.parameterPreparation.own_jets
      transition_jets := stage.parameterPreparation.transition_jets }
  have hInputFinite := parameterRound2_original_pair_on_compact_finite
    Data.atlas stage.parameterFamily stage.Omega stage.Q stage.source_compact stage.parameter_compact
    stage.source_target stage.parameter_target stage.oldMap hOld _ hHold r stage.t
  have hInputLe := round4ParameterSpatialPairWeighted_le_total Data.atlas stage.parameterFamily
    stage.oldMap (fun p x => (stage.delta^2)⁻¹ • (stage.metric p x -
      inducedMetric (I := 𝓘(ℝ,Es)) (fun y => stage.oldMap (p,y)) x))
    (incrementsOriginalEvaluation Data.atlas stage.parameterFamily.chart stage.Omega stage.Q univ)
    (fun _ _ hy => hy.1) hOld r stage.t
  have hInputBudget := (ENNReal.toReal_mono hInputFinite hInputLe).trans stage.old_pair_budget
  have hpair := (hm j).2 Data.parameterCount Data.atlas stage.parameterFamily
    stage.atlas_smooth stage.parameter_smooth stage.sourcePreparation RPclosed
    stage.buffer stage.Omega stage.Q stage.source_compact stage.parameter_compact stage.source_target
    stage.parameter_target stage.source_sampling stage.parameter_sampling
    stage.ell stage.ell stage.t stage.ell_pos le_rfl stage.ell_le_t stage.t_le_one
    stage.oldMap stage.oldMap_smooth _ hHold budget hInputBudget
  have hmle : parameterSpatialWeighted (n := n) (d := d) j stage.ell
      (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart) S ≤
      round4ParameterSpatialPairWeighted Data.atlas stage.parameterFamily Data.F
        (tensorLocalParameterSmoothing Data.atlas stage.parameterFamily stage.atlas_smooth
          (volume : Measure X) (fixedSmoothingKernel (volume : Measure X) radius hradius r) stage.ell
          (parameterLocalProductCutoff Data.atlas stage.parameterFamily
            (squareNormalizedCutoff stage.sourcePreparation.raw)
            (tensorLocalNormalizedCutoff stage.parameterPreparation.raw))
          (fun p x => (stage.delta^2)⁻¹ • (stage.metric p x -
            inducedMetric (I := 𝓘(ℝ,Es)) (fun y => stage.oldMap (p,y)) x))) j stage.ell (incrementsOriginalDifferentiation Data.atlas stage.parameterFamily.chart) := by
    rw [← stage.chart_eq]
    exact (parameterSpatialWeighted_mono_evaluation _ _ _ _ _ _
      (fun _ _ hy => by simpa only [stage.chart_eq] using hy.1)).trans (le_add_right le_rfl)
  dsimp only at hpair
  rw [← stage.map_eq] at hpair
  have hfin := ne_top_of_le_ne_top hpair.2.2.1 hmle
  have hbound := (ENNReal.toReal_mono hpair.2.2.1 hmle).trans hpair.2.2.2
  have hSF := round3_repair_stage_smoothed_map_contMDiff Data BS0 TS0 BP0 TP0
    hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r budget reference givenPacket stage
  have hcoords : ∀ a, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates Data.atlas Data.parameterChart Data.F a)
      (incrementsOriginalDifferentiation Data.atlas Data.parameterChart a) := by
    rw [← stage.chart_eq]
    exact parameterRound2_originalMapCoordinates_contDiffOn Data.atlas stage.parameterFamily.chart
      stage.atlas_smooth stage.parameter_smooth Data.F hSF
  have h := round4_original_spatial_fixed_chart_first_hessian_profiles T hT Data.atlas Data.parameterChart
    Data.F S hSO hcoords j stage.ell stage.ell_pos (stage.ell_le_t.trans stage.t_le_one)
    hfin (Cm j*budget) (mul_nonneg (hCm j) hbudget0) hbound i e O Z hO hZO
    hTransition hSource hParameter hSample hChartJets
  simpa only [round4SpatialStageProfile,mul_assoc] using h

#print axioms round4_actual_spatial_stage_first_hessian_profiles
#print axioms round4SpatialStageProfile_congr_prefix
end GlobalEmbedding.Continuation
