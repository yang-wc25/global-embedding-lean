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
local instance actualOriginalSmoothingStageDataChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance actualOriginalSmoothingStageDataIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

/-- Genuine inputs and literal bindings for one actual smoothing stage.
This record contains no derivative bound for SF, SH, the computed target,
any mean, or any correction. The budget is the original old map/tensor pair
on the actual full sampling domains. -/
structure ParameterRound2OriginalSmoothingStage
    (Data : IncrementsOriginalNativeData n d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (r : ℕ) (budget : ℝ) (reference givenPacket : ℕ → ℝ) where
  parameterFamily : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep
  chart_eq : parameterFamily.chart = Data.parameterChart
  atlas_smooth : IsSmoothBufferedAtlas Data.atlas
  parameter_smooth : ∀ i, parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P
  sourcePreparation : TensorRawCutoffPreparation Data.atlas BS0 TS0 Ds
  parameterPreparation : TensorLocalRawPreparation parameterFamily Data.parameterSet BP0 TP0 Dp
  buffer : radius ≤ min parameterFamily.buffer Data.atlas.buffer
  Omega : Fin Data.atlas.count → Set D
  Q : Fin Data.parameterCount → Set Ep
  source_compact : ∀ i, IsCompact (Omega i)
  parameter_compact : ∀ i, IsCompact (Q i)
  source_target : ∀ i, Omega i ⊆ (Data.atlas.chart i).target
  parameter_target : ∀ i, Q i ⊆ (parameterFamily.chart i).target
  source_sampling : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Omega i
  parameter_sampling : ∀ i, tensorLocalSamplingCoordinates parameterFamily i ⊆ Q i
  samples_compact : ∀ i, IsCompact (incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)
  samples_inner : ∀ i, incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ⊆
      tensorLocalOriginalInner Data.atlas parameterFamily Data.parameterSet i
  ell : ℝ
  t : ℝ
  ell_pos : 0 < ell
  ell_le_t : ell ≤ t
  t_le_one : t ≤ 1
  oldMap : P × M → V
  referenceMap : P × M → V
  oldMap_smooth : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ oldMap
  referenceMap_smooth : ContMDiff 𝓘(ℝ,Ep × D) 𝓘(ℝ,V) ∞ referenceMap
  reference_bound : ∀ j, (paperAtlasCj j (incrementsOriginalTensorCoordinates Data.atlas parameterFamily.chart
    (fun p x => inducedMetric (I := 𝓙) (fun y => referenceMap (p,y)) x))
    (incrementsOriginalDifferentiation Data.atlas parameterFamily.chart)
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)).toReal ≤ reference j
  metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x)
  metric_symmetric : ∀ p x, (metric p x).IsSymm
  metric_smooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas parameterFamily.chart metric i)
    (incrementsOriginalDifferentiation Data.atlas parameterFamily.chart i)
  delta : ℝ
  deltaNext : ℝ
  reserve_ratio : (deltaNext/delta)^2 ≤ 1
  old_pair_budget : (parameterLocalOriginalTotalPairWeighted Data.atlas parameterFamily oldMap
    (fun p x => (delta^2)⁻¹ • (metric p x-inducedMetric (I := 𝓙) (fun y => oldMap (p,y)) x)) r t
    (incrementsOriginalEvaluation Data.atlas parameterFamily.chart Omega Q univ)).toReal ≤ budget
  map_eq : Data.F = parameterLocalMapSmoothing (parameterLocalProductFamily Data.atlas parameterFamily)
    (volume : Measure (Ep × D)) (fixedSmoothingKernel (volume : Measure (Ep × D)) radius hradius r) ell
    (parameterLocalProductCutoff Data.atlas parameterFamily (squareNormalizedCutoff sourcePreparation.raw)
      (tensorLocalNormalizedCutoff parameterPreparation.raw)) oldMap
  target_eq : Data.H = fun p x => tensorLocalParameterSmoothing Data.atlas parameterFamily atlas_smooth
    (volume : Measure (Ep × D)) (fixedSmoothingKernel (volume : Measure (Ep × D)) radius hradius r) ell
    (parameterLocalProductCutoff Data.atlas parameterFamily (squareNormalizedCutoff sourcePreparation.raw)
      (tensorLocalNormalizedCutoff parameterPreparation.raw))
    (fun p x => (delta^2)⁻¹ • (metric p x-inducedMetric (I := 𝓙) (fun y => oldMap (p,y)) x)) p x -
    (deltaNext/delta)^2 • inducedMetric (I := 𝓙) (fun y => referenceMap (p,y)) x
  given_finite : ∀ j, parameterRound2_originalFixedPacketProfile Data j ell ≠ ⊤
  given_bound : ∀ j, (parameterRound2_originalFixedPacketProfile Data j ell).toReal ≤ givenPacket j

theorem exists_uniform_parameterRound2_original_stage_data_profiles
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (radius : ℝ) (hradius : 0 < radius) (r : ℕ) :
    ∃ Cmap : ℕ → ℝ, (∀ j, 0 ≤ Cmap j) ∧
    ∃ Ctarget : ℕ → ℝ, (∀ j, 0 ≤ Ctarget j) ∧ ∀
    (Data : IncrementsOriginalNativeData n d N M P) (budget : ℝ) (reference givenPacket : ℕ → ℝ)
    (stage : ParameterRound2OriginalSmoothingStage Data BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket),
    let S := incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet
    let W := incrementsOriginalParameterRegion Data
    ∃ H : parameterRound2_originalTensorGermSpace Data.atlas Data.parameterChart S W,
    H.val = Data.H ∧
    (∀ j, parameterRound2_originalTensorGermSeminorm Data.atlas Data.parameterChart S W stage.samples_compact
      (fun _ _ hy => hy.1) stage.ell j H ≤ Ctarget j*budget+(j+1)*reference j) ∧
    (∀ j, actualOriginalGivenInputProfile Data j stage.ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Data j stage.ell).toReal ≤
        max (Cmap j*budget) (max (Ctarget j*budget+(j+1)*reference j) (givenPacket j))) := by
  obtain ⟨Cmap,hCmap,Ctarget,hCtarget,hprod⟩ := exists_uniform_parameterRound2_original_smoothed_stage_profiles
    (n := n) (d := d) (N := N) (M := M) (P := P)
    BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp radius hradius r
  refine ⟨Cmap,hCmap,Ctarget,hCtarget,?_⟩
  intro Data budget reference givenPacket stage
  exact hprod Data stage.parameterFamily stage.chart_eq stage.atlas_smooth stage.parameter_smooth
    stage.sourcePreparation stage.parameterPreparation stage.buffer stage.Omega stage.Q
    stage.source_compact stage.parameter_compact stage.source_target stage.parameter_target
    stage.source_sampling stage.parameter_sampling stage.samples_compact stage.samples_inner
    stage.ell stage.t stage.ell_pos stage.ell_le_t stage.t_le_one stage.oldMap stage.referenceMap
    stage.oldMap_smooth stage.referenceMap_smooth reference stage.reference_bound stage.metric
    stage.metric_symmetric stage.metric_smooth stage.delta stage.deltaNext stage.reserve_ratio budget
    stage.old_pair_budget stage.map_eq stage.target_eq givenPacket stage.given_finite stage.given_bound

#print axioms exists_uniform_parameterRound2_original_stage_data_profiles
end GlobalEmbedding.Continuation
