import Smoothing.ParameterRound2OriginalSmoothedStageProfiles

/-!
Actual smoothing-stage inputs on the original compact norm domains. The
receiving norm domain is allowed to extend outside the atlas inner sets.
The original chart targets remain the differentiation domains, and the
physical parameter lies in the partition region by its evaluation-domain
definition. No smoothing gain or error estimate is included as an input.

This replaces the restrictive `samples_inner` premise of the earlier stage
record. The literal SF/SH formulas and every primitive sampling input stay
unchanged; full receiving-chart estimates supply the subsequent consumer.
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
local instance round3RepairOriginalStageChartedSpace : ChartedSpace (Ep × D) (P × M) :=
  prodChartedSpace Ep P D M
local instance round3RepairOriginalStageIsManifold : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

/-- Genuine inputs and literal bindings for one actual smoothing stage.
This record contains no derivative bound for SF, SH, the computed target,
any mean, or any correction. The budget is the original old map/tensor pair
on the actual full sampling domains. -/
structure Round3RepairOriginalSmoothingStage
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
  samples_sampling : ∀ i, incrementsOriginalEvaluation Data.atlas Data.parameterChart
    Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ⊆
      incrementsOriginalEvaluation Data.atlas parameterFamily.chart Omega Q univ i
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

/-- The actual original evaluation domain already lies in its differentiation
chart. No shrinking to an atlas inner set is required. -/
theorem round3_repair_original_stage_evaluation_target
    (Data : IncrementsOriginalNativeData n d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) :
    incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i ⊆
      incrementsOriginalDifferentiation Data.atlas Data.parameterChart i :=
  fun _ h => h.1

/-- The parameter portion of the original evaluation domain is exactly in K. -/
theorem round3_repair_original_stage_evaluation_parameter
    (Data : IncrementsOriginalNativeData n d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (y : Fin (n+d) → ℝ)
    (hy : y ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
      Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i) :
    (incrementsOriginalJointPoint Data.atlas Data.parameterChart i y).1 ∈ Data.parameterSet :=
  hy.2.2.2

end GlobalEmbedding.Continuation
