import Smoothing.Round3RepairOriginalSmoothingStageData
import Smoothing.Round3OuterComputedRepairControl
import Smoothing.ParameterRound2RepairIdentity

/-! Fixed original smoothing material and a literal current repair state.
The reference packet contains primitive cutoffs and sampling domains.  The
current state contains only the old map and its original normalized-defect
budget.  Its actual smoothing stage is assembled at the literal computed
map and target; no SF, SH, increment, or output bound is supplied. -/

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
local instance round3RepairPacketChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance round3RepairPacketIsManifold : IsManifold 𝓘(ℝ,Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := IT) (n := ∞) P M

/-- Original immutable smoothing material.  Both norm samples and convolution
sampling domains are stated explicitly.  In the closed-parameter application
these two domains are chosen equal at the outset. -/
structure Round3RepairFixedSmoothingPacket
    (Data : IncrementsOriginalNativeData n d N M P)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) (hradius : 0 < radius)
    (reference givenPacket : ℕ → ℝ) where
  domain : IncrementsOriginalDomainConditions Data
  parameterFamily : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep
  chart_eq : parameterFamily.chart = Data.parameterChart
  sourcePreparation : TensorRawCutoffPreparation Data.atlas BS0 TS0 Ds
  parameterPreparation : TensorLocalRawPreparation parameterFamily Data.parameterSet BP0 TP0 Dp
  buffer : radius ≤ min parameterFamily.buffer Data.atlas.buffer
  Omega : Fin Data.atlas.count → Set Es
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
  referenceMap : P × M → Ey
  referenceMap_smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ referenceMap
  reference_tensor : Data.H = fun p x => inducedMetric (I := IT) (fun y => referenceMap (p,y)) x
  reference_eq : Data.reference = Data.H
  reference_bound : ∀ j, (paperAtlasCj j (incrementsOriginalTensorCoordinates Data.atlas parameterFamily.chart
    (fun p x => inducedMetric (I := IT) (fun y => referenceMap (p,y)) x))
    (incrementsOriginalDifferentiation Data.atlas parameterFamily.chart)
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet)).toReal ≤ reference j
  given_finite : ∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤
  given_bound : ∀ j, (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ givenPacket j
  metric : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace IT x)
  metric_symmetric : ∀ p x, (metric p x).IsSymm
  metric_smooth : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas parameterFamily.chart metric i)
    (incrementsOriginalDifferentiation Data.atlas parameterFamily.chart i)

variable {Data : IncrementsOriginalNativeData n d N M P}
  {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
  {reference givenPacket : ℕ → ℝ}

/-- An actual current map and its current normalized defect.  All derivative
budgets are on the old map/tensor pair, before applying either smoother. -/
structure Round3RepairCurrentSmoothingState
    (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
    (r : ℕ) (budget : ℝ) where
  oldMap : P × M → Ey
  oldMap_smooth : ContMDiff 𝓘(ℝ,Ep × Es) 𝓘(ℝ,Ey) ∞ oldMap
  ell : ℝ
  t : ℝ
  ell_pos : 0 < ell
  ell_le_t : ell ≤ t
  t_le_one : t ≤ 1
  delta : ℝ
  deltaNext : ℝ
  reserve_ratio : (deltaNext/delta)^2 ≤ 1
  old_pair_budget : (parameterLocalOriginalTotalPairWeighted Data.atlas packet.parameterFamily oldMap
    (fun p x => (delta^2)⁻¹ • (packet.metric p x-inducedMetric (I := IT) (fun y => oldMap (p,y)) x)) r t
    (incrementsOriginalEvaluation Data.atlas packet.parameterFamily.chart packet.Omega packet.Q univ)).toReal ≤ budget

namespace Round3RepairCurrentSmoothingState
variable (packet : Round3RepairFixedSmoothingPacket Data BS0 TS0 BP0 TP0 Ds Dp radius hradius reference givenPacket)
  {r : ℕ} {budget : ℝ} (state : Round3RepairCurrentSmoothingState packet r budget)

def normalizedDefect (p : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace IT x) :=
  (state.delta^2)⁻¹ • (packet.metric p x-inducedMetric (I := IT) (fun y => state.oldMap (p,y)) x)

def smoothedMap : P × M → Ey :=
  parameterLocalMapSmoothing (parameterLocalProductFamily Data.atlas packet.parameterFamily)
    (volume : Measure (Ep × Es)) (fixedSmoothingKernel (volume : Measure (Ep × Es)) radius hradius r) state.ell
    (parameterLocalProductCutoff Data.atlas packet.parameterFamily (squareNormalizedCutoff packet.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff packet.parameterPreparation.raw)) state.oldMap

def computedTarget (p : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace IT x) :=
  tensorLocalParameterSmoothing Data.atlas packet.parameterFamily packet.domain.atlas_smooth
    (volume : Measure (Ep × Es)) (fixedSmoothingKernel (volume : Measure (Ep × Es)) radius hradius r) state.ell
    (parameterLocalProductCutoff Data.atlas packet.parameterFamily (squareNormalizedCutoff packet.sourcePreparation.raw)
      (tensorLocalNormalizedCutoff packet.parameterPreparation.raw)) (state.normalizedDefect packet) p x -
    (state.deltaNext/state.delta)^2 • Data.H p x

def computedData (U : Set P) (reserve : ℝ) : IncrementsOriginalNativeData n d N M P :=
  round3OriginalComputedPositiveData Data (state.smoothedMap packet) (state.computedTarget packet) U reserve

theorem computed_fixed_packet (U : Set P) (reserve : ℝ) (j : ℕ) (ell : ℝ) :
    parameterRound2_originalFixedPacketProfile (state.computedData packet U reserve) j ell =
      parameterRound2_originalFixedPacketProfile Data j ell := rfl

/-- The actual stage is a definition from the old state and fixed packet.
Its map and target are literal SF and SH-(deltaNext/delta)^2 gamma(F0). -/
def toStage (U : Set P) (reserve : ℝ) :
    Round3RepairOriginalSmoothingStage (state.computedData packet U reserve)
      BS0 TS0 BP0 TP0 Ds Dp radius hradius r budget reference givenPacket where
  parameterFamily := packet.parameterFamily
  chart_eq := packet.chart_eq
  atlas_smooth := packet.domain.atlas_smooth
  parameter_smooth := by rw [packet.chart_eq]; exact packet.domain.parameter_charts_smooth
  sourcePreparation := packet.sourcePreparation
  parameterPreparation := packet.parameterPreparation
  buffer := packet.buffer
  Omega := packet.Omega
  Q := packet.Q
  source_compact := packet.source_compact
  parameter_compact := packet.parameter_compact
  source_target := packet.source_target
  parameter_target := packet.parameter_target
  source_sampling := packet.source_sampling
  parameter_sampling := packet.parameter_sampling
  samples_compact := packet.samples_compact
  samples_sampling := packet.samples_sampling
  ell := state.ell
  t := state.t
  ell_pos := state.ell_pos
  ell_le_t := state.ell_le_t
  t_le_one := state.t_le_one
  oldMap := state.oldMap
  referenceMap := packet.referenceMap
  oldMap_smooth := state.oldMap_smooth
  referenceMap_smooth := packet.referenceMap_smooth
  reference_bound := packet.reference_bound
  metric := packet.metric
  metric_symmetric := packet.metric_symmetric
  metric_smooth := packet.metric_smooth
  delta := state.delta
  deltaNext := state.deltaNext
  reserve_ratio := state.reserve_ratio
  old_pair_budget := state.old_pair_budget
  map_eq := rfl
  target_eq := by
    change state.computedTarget packet = _
    unfold computedTarget normalizedDefect
    rw [packet.reference_tensor]
    rfl
  given_finite := fun j => by
    rw [state.computed_fixed_packet packet]
    exact ne_top_of_le_ne_top (packet.given_finite j)
      (parameterRound2_originalFixedPacketProfile_mono_scale Data j state.ell 1
        (state.ell_le_t.trans state.t_le_one))
  given_bound := fun j => by
    rw [state.computed_fixed_packet packet]
    exact (ENNReal.toReal_mono (packet.given_finite j)
      (parameterRound2_originalFixedPacketProfile_mono_scale Data j state.ell 1
        (state.ell_le_t.trans state.t_le_one))).trans (packet.given_bound j)

theorem normalizedDefect_smooth :
    ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates Data.atlas packet.parameterFamily.chart
      (state.normalizedDefect packet) i)
      (incrementsOriginalDifferentiation Data.atlas packet.parameterFamily.chart i) := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hMetric := parameterRound2_inducedMetric_originalCoordinates_contDiffOn Data.atlas
    packet.parameterFamily.chart packet.domain.atlas_smooth hB state.oldMap state.oldMap_smooth
  intro i
  exact ((packet.metric_smooth i).sub (hMetric i)).const_smul ((state.delta^2)⁻¹)

theorem normalizedDefect_symmetric (p : P) (x : M) :
    (state.normalizedDefect packet p x).IsSymm := by
  exact ((packet.metric_symmetric p x).sub (inducedMetric_isPosSemidef (I := IT) (fun y => state.oldMap (p,y)) x).isSymm).smul _

end Round3RepairCurrentSmoothingState
end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.Round3RepairCurrentSmoothingState.toStage
#print axioms GlobalEmbedding.Continuation.Round3RepairCurrentSmoothingState.normalizedDefect_smooth
