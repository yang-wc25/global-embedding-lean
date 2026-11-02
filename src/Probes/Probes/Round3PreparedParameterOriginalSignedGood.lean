import Probes.Round3PreparedParameterSignedLegality
import Probes.Round3ParameterOriginalPrimarySamples

/-! The original RS/RP preparations internally supply all physical parents
and all true original parameter samples for the fixed signed-secondary
packet. No prepared secondary family is a caller premise. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
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

 theorem round3_prepared_actual_original_parameter_signed_good
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hp : IncrementsOriginalPhaseConditions Ref hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Ref) (hAll : Ref.parameterSet = univ)
    (hF0joint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ Ref.F)
    (BS0 TS0 BP0 TP0 : ℕ → ℝ)
    (hBS0 : ∀ j, 0 ≤ BS0 j) (hTS0 : ∀ j, 0 ≤ TS0 j)
    (hBP0 : ∀ j, 0 ≤ BP0 j) (hTP0 : ∀ j, 0 ≤ TP0 j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS0 TS0 Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP0 TP0 Dp)
    (hOmega : ∀ i, IsCompact (Ref.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Ref.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Ref.atlas i ⊆ Ref.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Ref.parameterNormDomain i) :
    ∃ epsilon : ℝ, 0 < epsilon ∧ ∀ (F : P → M → Ey)
      (hFjoint : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞ (Function.uncurry F))
      (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p)),
    let S := incrementsOriginalEvaluation Ref.atlas Ref.parameterChart
      Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet
    paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S ≠ ⊤ →
    (paperAtlasCj 2 (incrementsOriginalMapCoordinates Ref.atlas Ref.parameterChart
      (fun z => F z.1 z.2-Ref.F z))
      (incrementsOriginalDifferentiation Ref.atlas Ref.parameterChart) S).toReal ≤ epsilon →
    ∀ (r : ActualSecondarySignedRecord (Fin Ref.primaryCount)) z,
      z ∈ tsupport (Ref.cutoff r.val.1.1) ∩ tsupport (Ref.cutoff r.val.1.2) →
      GoodCovector (F z.1) (hF z.1) z.2
        ((tangentSpaceCastModel 𝓘(ℝ,ℝ) (round3PreparedPhysicalSignedPhase Ref r z)).toContinuousLinearMap.comp
          (mfderiv 𝓙 𝓘(ℝ,ℝ) (fun x => round3PreparedPhysicalSignedPhase Ref r (z.1,x)) z.2)) := by
  obtain ⟨packet,hPart,hCount,hSupport,hParam⟩ :=
    round3_prepared_actual_original_parameter_secondary_factory Ref hd hs hp hImm hAll
      BS0 TS0 BP0 TP0 hBS0 hTS0 hBP0 hTP0 Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  exact round3_prepared_parameter_packet_signed_good Ref hd hs hAll _ packet hPart hSupport hParam hF0joint

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_original_parameter_signed_good
