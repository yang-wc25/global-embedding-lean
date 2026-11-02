import Probes.Round3PreparedReferenceInputProfile
import NormalPolar.PassiveOriginalGivenScale

/-! The real fixed smoothing packet supplies the complete reference Given
profile at every derivative order. Map and tensor finiteness come from the
actual smooth reference on the original compact samples. The remaining
phase/normal/cutoff/linear/transition packet is exactly the provided fixed
input. No constructed output or all-scale Given budget is assumed. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem passiveOriginal_fixed_reference_given_finite
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (packet : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp radius hradius reference Given)
    (hReference : Ref.F = packet.referenceMap) (hK : Ref.parameterSet = univ)
    (hOmega : Ref.sourceNormDomain = packet.Omega) (hQ : Ref.parameterNormDomain = packet.Q) :
    ∀ j, actualOriginalGivenInputProfile Ref j 1 ≠ ⊤ := by
  have hB : ∀ i, packet.parameterFamily.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [packet.chart_eq]
    exact packet.domain.parameter_charts_smooth
  have hMapSmooth := parameterRound2_originalMapCoordinates_contDiffOn Ref.atlas packet.parameterFamily.chart
    packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hTensorSmooth : ∀ i, ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates Ref.atlas packet.parameterFamily.chart Ref.H i)
      (incrementsOriginalDifferentiation Ref.atlas packet.parameterFamily.chart i) := by
    rw [packet.reference_tensor]
    exact parameterRound2_inducedMetric_originalCoordinates_contDiffOn Ref.atlas packet.parameterFamily.chart
      packet.domain.atlas_smooth hB packet.referenceMap packet.referenceMap_smooth
  have hSamples := packet.originalSamples_eq_closed hK hOmega hQ
  intro j
  have hMapFinite : paperAtlasCj (j+2)
      (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart Ref.F)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤ := by
    rw [hSamples,hReference,← packet.chart_eq]
    exact parameterRound2_paperAtlasCj_finite_of_compact _ _ _
      (parameterRound2_originalDifferentiation_open Ref.atlas packet.parameterFamily.chart)
      packet.closedSamples_compact (fun _ _ hy => hy.1) hMapSmooth (j+2)
  have hTensorFinite : paperAtlasCj (j+0)
      (incrementsOriginalTensorCoordinates Ref.atlas Ref.parameterChart Ref.H)
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart)
      (incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain
        Ref.parameterNormDomain Ref.parameterSet) ≠ ⊤ := by
    rw [hSamples,← packet.chart_eq]
    exact parameterRound2_paperAtlasCj_finite_of_compact _ _ _
      (parameterRound2_originalDifferentiation_open Ref.atlas packet.parameterFamily.chart)
      packet.closedSamples_compact (fun _ _ hy => hy.1) hTensorSmooth (j+0)
  have hm := parameterRound2_paperAtlasWeighted_finite_of_topOrder 2 j 1 _ _ _ hMapFinite
  have ht := parameterRound2_paperAtlasWeighted_finite_of_topOrder 0 j 1 _ _ _ hTensorFinite
  rw [parameterRound2_originalGivenProfile_eq_map_tensor_packet]
  exact (max_lt (lt_top_iff_ne_top.mpr hm)
    (max_lt (lt_top_iff_ne_top.mpr ht) (lt_top_iff_ne_top.mpr (packet.given_finite j)))).ne

theorem passiveOriginal_fixed_reference_given_budget
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    {BS TS BP TP : ℕ → ℝ} {Ds Dp : ℕ} {radius : ℝ} {hradius : 0 < radius}
    {reference Given : ℕ → ℝ}
    (packet : Round3RepairFixedSmoothingPacket Ref BS TS BP TP Ds Dp radius hradius reference Given)
    (hReference : Ref.F = packet.referenceMap) (hK : Ref.parameterSet = univ)
    (hOmega : Ref.sourceNormDomain = packet.Omega) (hQ : Ref.parameterNormDomain = packet.Q) :
    ∀ j ell, 0 < ell → ell ≤ 1 →
      actualOriginalGivenInputProfile Ref j ell ≠ ⊤ ∧
      (actualOriginalGivenInputProfile Ref j ell).toReal ≤
        (actualOriginalGivenInputProfile Ref j 1).toReal :=
  passiveOriginal_given_fixed_scale_budget Ref
    (passiveOriginal_fixed_reference_given_finite Ref packet hReference hK hOmega hQ)

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.passiveOriginal_fixed_reference_given_finite
#print axioms GlobalEmbedding.Continuation.passiveOriginal_fixed_reference_given_budget
