import Repair.EndpointFiniteFixedBudget
import Smoothing.Round3RepairCurrentState

/-! Construct the actual smoothing packet from the original fixed chart
geometry and the proved fixed-packet finiteness. The default metric is the
reference induced metric; arbitrary target metrics are installed only
after the numerical entrance radius has been selected. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold Set Function
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin n)
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
private local instance smoothingGeomProductChart : ChartedSpace X (P × M) := prodChartedSpace Ep P D M
private local instance smoothingGeomProductManifold : IsManifold 𝓘(ℝ,X) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓘(ℝ,D)) (n := ∞) P M

/-- Only original charts, raw covering bumps, fixed geometric jet budgets,
buffers and the literal compact norm domains are fields. -/
structure RepairOriginalSmoothingGeometry
    (Data : IncrementsOriginalNativeData n d N M P)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) where
  parameterFamily : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep
  chart_eq : parameterFamily.chart=Data.parameterChart
  sourcePreparation : TensorRawCutoffPreparation Data.atlas BS TS Ds
  parameterPreparation : TensorLocalRawPreparation parameterFamily Data.parameterSet BP TP Dp
  buffer : radius ≤ min parameterFamily.buffer Data.atlas.buffer
  source_compact : ∀ i, IsCompact (Data.sourceNormDomain i)
  parameter_compact : ∀ i, IsCompact (Data.parameterNormDomain i)
  source_sampling : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i
  parameter_sampling : ∀ i, tensorLocalSamplingCoordinates parameterFamily i ⊆ Data.parameterNormDomain i

def repairOriginalActualReferenceProfile
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) : ℝ :=
  (paperAtlasCj j (incrementsOriginalTensorCoordinates Data.atlas Data.parameterChart Data.H)
    (incrementsOriginalDifferentiation Data.atlas Data.parameterChart)
    (incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
      Data.parameterNormDomain Data.parameterSet)).toReal

def repairOriginalActualGivenProfile
    (Data : IncrementsOriginalNativeData n d N M P) (j : ℕ) : ℝ :=
  (parameterRound2_originalFixedPacketProfile Data j 1).toReal

/-- This is a construction of the actual packet. Its reference bounds are
literal original norms; its all-order Given finiteness is supplied by the
actual finite-reference-budget producer. There is no initialized state,
ideal increment, solver output, target derivative budget or limit here. -/
def repair_original_actual_smoothing_packet
    (Data : IncrementsOriginalNativeData n d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hOpen : Data.parameterOpen=univ) (hAll : Data.parameterSet=univ)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ) (radius : ℝ) (hRadius : 0 < radius)
    (geometry : RepairOriginalSmoothingGeometry Data BS TS BP TP Ds Dp radius)
    (hReference : Data.H = fun p x => inducedMetric (I := 𝓘(ℝ,D)) (fun y => Data.F (p,y)) x)
    (hReferenceEq : Data.reference=Data.H)
    (hGiven : ∀ j, parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤) :
    Round3RepairFixedSmoothingPacket Data BS TS BP TP Ds Dp radius hRadius
      (repairOriginalActualReferenceProfile Data) (repairOriginalActualGivenProfile Data) where
  domain := hd
  parameterFamily := geometry.parameterFamily
  chart_eq := geometry.chart_eq
  sourcePreparation := geometry.sourcePreparation
  parameterPreparation := geometry.parameterPreparation
  buffer := geometry.buffer
  Omega := Data.sourceNormDomain
  Q := Data.parameterNormDomain
  source_compact := geometry.source_compact
  parameter_compact := geometry.parameter_compact
  source_target := hd.source_norm_subset
  parameter_target := by rw [geometry.chart_eq]; exact hd.parameter_norm_subset
  source_sampling := geometry.source_sampling
  parameter_sampling := geometry.parameter_sampling
  samples_compact := by
    rw [hAll]
    exact parameterRound2_originalEvaluation_univ_compact Data.atlas Data.parameterChart _ _
      geometry.source_compact geometry.parameter_compact hd.source_norm_subset hd.parameter_norm_subset
  samples_sampling := by rw [geometry.chart_eq,hAll]; exact fun _ => Subset.rfl
  referenceMap := Data.F
  referenceMap_smooth := (parameterRound2_original_full_parameter_coordinates Data hd hs hOpen).1
  reference_tensor := hReference
  reference_eq := hReferenceEq
  reference_bound := by
    intro j
    rw [geometry.chart_eq,← hReference]
    exact le_rfl
  given_finite := hGiven
  given_bound := fun _ => le_rfl
  metric := Data.H
  metric_symmetric := by
    rw [hReference]
    intro p x
    exact (inducedMetric_isPosSemidef (I := 𝓘(ℝ,D)) (fun y => Data.F (p,y)) x).isSymm
  metric_smooth := by
    rw [geometry.chart_eq]
    exact (parameterRound2_original_full_parameter_coordinates Data hd hs hOpen).2.2

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_original_actual_smoothing_packet
