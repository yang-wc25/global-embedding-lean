import CollarCompletion.OriginalParentSampling
import CompletionIntegration.PointwiseObserverJets
import CompletionIntegration.PreparedSecondaryNativeProfiles
import IncrementsCompletion.PositiveSecondaryPacketProfiles

/-!
# Actual signed packet positive profiles on the unchanged original samples

The fixed packet itself supplies its native chart budgets. Its physical
carrier lies in the same localized original parent, which places the true
owner point in the original Q/Omega by `OriginalParentSampling`. Applying
the pointwise observer lemma then constructs the positive observer/inverse
profiles. They are selected before ell and observation order.

This theorem supplies only the positive-chart field of the existing
secondary packet profile record. It does not assume or construct the cutoff
field. It also makes no new uniform finite-entrance claim for the qualitative
adapted pieces from which the native budgets are obtained.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation.CollarCompletion

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem original_secondary_packet_positive_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (Parameter Spatial : ℕ → ℝ)
    (hParameterNonneg : ∀ k, 0 ≤ Parameter k) (hSpatialNonneg : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ packet : Round3PreparedParameterSecondaryPacket Data hd hs theta,
    ∃ Tinv Tobs : ℕ → ℝ, (∀ k, 0 ≤ Tinv k) ∧ (∀ k, 0 ≤ Tobs k) ∧
      ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer k, 1 ≤ k →
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      let native := (choice.pullback (Data.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans native.chart
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
        ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Data r choice →
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Tobs k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Tinv k := by
  intro theta packet
  obtain ⟨NF,NI,hNF,hNI,hForward,hInverse⟩ :=
    prepared_secondary_native_chart_profiles Data hd hs theta packet
  let Tobs := repairEntranceCompositionProfile
    (repairEntranceConjugatedForwardProfile NF Parameter Parameter) Spatial
  let Tinv := repairEntranceCompositionProfile Spatial
    (repairEntranceConjugatedForwardProfile NI Parameter Parameter)
  have hCF : ∀ k, 0 ≤ repairEntranceConjugatedForwardProfile NF Parameter Parameter k :=
    repairEntranceCompositionProfile_nonneg Parameter (repairEntranceCompositionProfile NF Parameter)
      hParameterNonneg (repairEntranceCompositionProfile_nonneg NF Parameter hNF hParameterNonneg)
  have hCI : ∀ k, 0 ≤ repairEntranceConjugatedForwardProfile NI Parameter Parameter k :=
    repairEntranceCompositionProfile_nonneg Parameter (repairEntranceCompositionProfile NI Parameter)
      hParameterNonneg (repairEntranceCompositionProfile_nonneg NI Parameter hNI hParameterNonneg)
  refine ⟨Tinv,Tobs,
    repairEntranceCompositionProfile_nonneg Spatial _ hSpatialNonneg hCI,
    repairEntranceCompositionProfile_nonneg _ Spatial hCF hSpatialNonneg,?_⟩
  intro ell hell hell1 r i a observer k hk choice native t z hz hCarrier
  let piece := packet.piece r i a
  have hPreserves : Round3ParameterChartPreserves piece.native :=
    (round3_prepared_signed_native_preserves_phase Data hd hs i r _ piece).1
  have hActualChart : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1)
      (round3ParameterCrossNativeChart (Data.parameterChart i.2)
        (Data.parameterChart observer.2) piece.native) :=
    (round3Parameter_cross_host_conjugation (Data.parameterChart i.2)
      (Data.parameterChart observer.2) (Data.atlas.chart i.1) piece.native hPreserves).symm
  have hEvaluation := (actual_original_native_evaluation_iff Data hd observer z).mp hz
  have hpTarget : z.1 ∈ (Data.parameterChart observer.2).target :=
    hd.parameter_norm_subset observer.2 hEvaluation.2.1
  have hxTarget : z.2 ∈ (Data.atlas.chart observer.1).target :=
    hd.source_norm_subset observer.1 hEvaluation.1
  have hPhysicalParent := packet.parent r i a hCarrier.1
  have hOwn := original_parameter_localized_parent_original_samples Data B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter psi i observer z hPhysicalParent
  have hPhysicalSource := packet.source r i a hCarrier
  have hNativeSource : (z.1,(Data.atlas.chart observer.1).symm z.2) ∈ native.chart.source := by
    change _ ∈ (round3ParameterChartPullback (Data.parameterChart observer.2) choice.chart).source
    exact (round3ParameterChartPullback_source_iff (Data.parameterChart observer.2) choice.chart
      (round3_prepared_parameter_secondary_preserves Data hd hs i r _ piece)
      (z.1,(Data.atlas.chart observer.1).symm z.2) hpTarget).mpr hPhysicalSource
  have hTSource : z ∈ t.source := ⟨⟨mem_univ _,hxTarget⟩,hNativeSource⟩
  have hPoint := completion_original_native_observer_positive_jets_at Data hd i.2 i.1
    piece.native (actualOriginalParameterSignedPhase Data i r.val) piece.slices piece.data hPreserves
    NF NI Parameter Spatial hNF hNI hParameterNonneg hSpatialNonneg transition
    (hForward r i a) (hInverse r i a) observer z hEvaluation.2.1 hEvaluation.1 hOwn.1 hOwn.2
  have hOriginalT : t = ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
      (actualHostAdaptedChart (Data.atlas.chart i.1)
        (round3ParameterCrossNativeChart (Data.parameterChart i.2)
          (Data.parameterChart observer.2) piece.native)) := by
    dsimp only [t]
    rw [hActualChart]
  have hPointAt := hPoint (hOriginalT ▸ hTSource) k hk
  rw [← hOriginalT] at hPointAt
  have hWeight : ell^(k-1) ≤ 1 := pow_le_one₀ hell hell1
  exact ⟨(mul_le_of_le_one_left (norm_nonneg _) hWeight).trans hPointAt.1,
    (mul_le_of_le_one_left (norm_nonneg _) hWeight).trans hPointAt.2⟩

end GlobalEmbedding.Continuation.CollarCompletion
#print axioms GlobalEmbedding.Continuation.CollarCompletion.original_secondary_packet_positive_profiles
