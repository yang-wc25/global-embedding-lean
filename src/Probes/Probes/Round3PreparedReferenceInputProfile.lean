import Probes.Round3RepairReferenceEnvelope
import Smoothing.ParameterRound2OriginalFixedPacket

/-! The fixed reference packet supplies its own original zero-order
CORE-plus-linear entrance. Only the actual reference C2 map norm, C0 tensor
norm and provided fixed packet are used. No current-stage or output budget
is a premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

 theorem round3_prepared_actual_reference_linear_profile
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS0 TS0 BP0 TP0 : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (packet : Round3RepairFixedSmoothingPacket Ref BS0 TS0 BP0 TP0 Ds Dp radius hradius reference Given)
    (hReference : Ref.F = packet.referenceMap) (hK : Ref.parameterSet = univ)
    (hOmega : Ref.sourceNormDomain = packet.Omega) (hQ : Ref.parameterNormDomain = packet.Q) :
    incrementsOriginalInputProfileWithLinear Ref 0 1 ≠ ⊤ ∧
      (incrementsOriginalInputProfileWithLinear Ref 0 1).toReal ≤
        max (round3RepairReferenceLowBase packet) (Given 0) := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  let mapNorm := paperAtlasCj 2
    (incrementsOriginalMapCoordinates Ref.atlas packet.parameterFamily.chart packet.referenceMap)
    (incrementsOriginalDifferentiation Ref.atlas packet.parameterFamily.chart) packet.closedSamples
  let tensorNorm := paperAtlasCj 0
    (incrementsOriginalTensorCoordinates Ref.atlas packet.parameterFamily.chart Ref.H)
    (incrementsOriginalDifferentiation Ref.atlas packet.parameterFamily.chart) packet.closedSamples
  have hMapSmooth := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hTensorSmooth : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates Ref.atlas packet.parameterFamily.chart Ref.H i)
      (incrementsOriginalDifferentiation Ref.atlas packet.parameterFamily.chart i) := by
    rw [packet.reference_tensor]
    exact parameterRound2_inducedMetric_originalCoordinates_contDiffOn Ref.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hMapFinite : mapNorm ≠ ⊤ := parameterRound2_paperAtlasCj_finite_of_compact _ _ _
    (parameterRound2_originalDifferentiation_open Ref.atlas packet.parameterFamily.chart)
    packet.closedSamples_compact (fun _ _ hy => hy.1) hMapSmooth 2
  have hTensorFinite : tensorNorm ≠ ⊤ := parameterRound2_paperAtlasCj_finite_of_compact _ _ _
    (parameterRound2_originalDifferentiation_open Ref.atlas packet.parameterFamily.chart)
    packet.closedSamples_compact (fun _ _ hy => hy.1) hTensorSmooth 0
  have hSamples := packet.originalSamples_eq_closed hK hOmega hQ
  have hMapEq : paperAtlasWeighted 2 0 1
      (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet) =
      mapNorm := by
    simp only [paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,pow_zero,one_mul,zero_add]
    rw [hSamples,hReference,← packet.chart_eq]
  have hTensorEq : paperAtlasWeighted 0 0 1
      (incrementsOriginalTensorCoordinates Ref.atlas Ref.parameterChart Ref.H)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet) =
      tensorNorm := by
    simp only [paperAtlasWeighted,Finset.range_one,Finset.sum_singleton,pow_zero,one_mul,zero_add]
    rw [hSamples,← packet.chart_eq]
  have hGiven := parameterRound2_originalGivenProfile_of_actual_map_tensor Ref 0 1 le_rfl
    mapNorm.toReal tensorNorm.toReal (Given 0)
    (by rw [hMapEq]; exact hMapFinite) (by rw [hMapEq])
    (by rw [hTensorEq]; exact hTensorFinite) (by rw [hTensorEq])
    (packet.given_finite 0) (packet.given_bound 0)
  have hLinear := actualOriginalGivenInputProfile_linear_le Ref 0 1
  refine ⟨ne_top_of_le_ne_top hGiven.1 hLinear,
    ((ENNReal.toReal_mono hGiven.1 hLinear).trans hGiven.2).trans ?_⟩
  change max mapNorm.toReal (max tensorNorm.toReal (Given 0)) ≤
    max (mapNorm.toReal+tensorNorm.toReal) (Given 0)
  apply max_le
  · exact (le_add_of_nonneg_right ENNReal.toReal_nonneg).trans (le_max_left _ _)
  · exact max_le ((le_add_of_nonneg_left ENNReal.toReal_nonneg).trans (le_max_left _ _))
      (le_max_right _ _)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_reference_linear_profile
