import OriginalIncrements.LocalizedSourceSampleSecondaryProfiles
import Repair.EntrancePointwiseOriginalObserverJets
import CollarCompletion.OriginalParentSampling

/-!
# Secondary observer profiles from actual parent-carrier samples

Only the physical parent support is sampled in the unchanged original
Omega/Q norm domains. The construction chart may cross their boundaries.
The same packet and numerical profiles are retained, and the owner samples
are manufactured directly from the original raw source/parameter parents.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter Manifold IsManifold
open scoped ContDiff Topology Classical BigOperators
namespace GlobalEmbedding.Continuation.OriginalIncrements

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "Z" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
private local instance : ChartedSpace (Ep × D) (P × M) := prodChartedSpace Ep P D M
private local instance : IsManifold 𝓘(ℝ,Ep × D) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ,Ep)) (I' := 𝓙) (n := ∞) P M

local notation "X" => Ep × D

structure CarrierSampleSecondaryChartBudget
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta) where
  mu : ℝ
  Mb : ℝ
  buffer : ℝ
  mu_pos : 0 < mu
  Mb_nonneg : 0 ≤ Mb
  buffer_pos : 0 < buffer
  nativeForward : ℕ → ℝ
  nativeInverse : ℕ → ℝ
  parameterTransition : ℕ → ℝ
  sourceTransition : ℕ → ℝ
  nativeForward_nonneg : ∀ j, 0 ≤ nativeForward j
  nativeInverse_nonneg : ∀ j, 0 ≤ nativeInverse j
  parameterTransition_nonneg : ∀ j, 0 ≤ parameterTransition j
  sourceTransition_nonneg : ∀ j, 0 ≤ sourceTransition j
  transition : RepairOriginalTransitionBudgets Ref parameterTransition sourceTransition
  forward : ∀ r i a j z, z ∈ (packet.piece r i a).native.source →
    ‖iteratedFDeriv ℝ j (packet.piece r i a).native z‖ ≤ nativeForward j
  inverse : ∀ r i a j z, z ∈ (packet.piece r i a).native.target →
    ‖iteratedFDeriv ℝ j (packet.piece r i a).native.symm z‖ ≤ nativeInverse j
  samples : ∀ i z, z ∈ tsupport (theta i) →
    (Ref.parameterChart i.2) z.1 ∈ Ref.parameterNormDomain i.2 ∧
      (Ref.atlas.chart i.1) z.2 ∈ Ref.sourceNormDomain i.1
  parameterValue : ℝ
  sourceValue : ℝ
  parameterValue_nonneg : 0 ≤ parameterValue
  sourceValue_nonneg : 0 ≤ sourceValue
  parameter_value : ∀ ip z, z ∈ Ref.parameterNormDomain ip → ‖z‖ ≤ parameterValue
  source_value : ∀ ih z, z ∈ Ref.sourceNormDomain ih → ‖z‖ ≤ sourceValue
  literal : ∀ r i a, (packet.piece r i a).cutoff = actualHostRefinementCutoff
    (actualOriginalHostJointChart («Ep» := Ep) (Ref.atlas.chart i.1))
    (round3ParameterNativeParent (Ref.parameterChart i.2) (theta i))
    (actualRefinementCutoff X (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val)
  scalar : ∀ r i j (a : packet.s r i) x,
    buffer^j*‖iteratedFDeriv ℝ j
      (actualRefinementCutoff X (packet.s r i) (buffer/actualPhaseRefinementFactor mu Mb) a.val) x‖ ≤
        (actualPhaseRefinementFactor mu Mb)^j*actualRefinementCutoffJetCost X j

namespace CarrierSampleSecondaryChartBudget
variable {Ref : IncrementsOriginalNativeData (m+1) d N M P}
  {hd : IncrementsOriginalDomainConditions Ref} {hs : IncrementsOriginalSmoothInputs Ref}
  {theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ}
  {packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta}
  (budget : CarrierSampleSecondaryChartBudget Ref hd hs theta packet)

def forwardProfile : ℕ → ℝ := repairEntranceOriginalForwardProfile budget.parameterValue
  budget.nativeForward budget.parameterTransition budget.sourceTransition

def inverseProfile : ℕ → ℝ := repairEntranceOriginalInverseProfile budget.parameterValue budget.sourceValue
  budget.nativeInverse budget.parameterTransition budget.sourceTransition

def cutoffProfile (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ) : ℕ → ℝ :=
  incrementSecondaryCutoffProfile X budget.mu budget.Mb budget.buffer BS TS BP TP Ds Dp

theorem forwardProfile_nonneg (j : ℕ) : 0 ≤ budget.forwardProfile j := by
  unfold forwardProfile repairEntranceOriginalForwardProfile
  split_ifs
  · exact le_max_of_le_left budget.parameterValue_nonneg
  · exact repairEntranceCompositionProfile_nonneg _ _
      (repairEntranceCompositionProfile_nonneg _ _ budget.parameterTransition_nonneg
        (repairEntranceCompositionProfile_nonneg _ _ budget.nativeForward_nonneg budget.parameterTransition_nonneg))
      budget.sourceTransition_nonneg j

theorem inverseProfile_nonneg (j : ℕ) : 0 ≤ budget.inverseProfile j := by
  unfold inverseProfile repairEntranceOriginalInverseProfile
  split_ifs
  · exact le_max_of_le_left budget.parameterValue_nonneg
  · exact repairEntranceCompositionProfile_nonneg _ _ budget.sourceTransition_nonneg
      (repairEntranceCompositionProfile_nonneg _ _ budget.parameterTransition_nonneg
        (repairEntranceCompositionProfile_nonneg _ _ budget.nativeInverse_nonneg budget.parameterTransition_nonneg)) j

theorem cutoffProfile_nonneg (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (j : ℕ) :
    0 ≤ budget.cutoffProfile BS TS BP TP Ds Dp j :=
  incrementSecondaryCutoffProfile_nonneg X budget.mu budget.Mb budget.buffer BS TS BP TP Ds Dp j
    budget.mu_pos budget.Mb_nonneg budget.buffer_pos hBS hTS hBP hTP

end CarrierSampleSecondaryChartBudget

theorem carrier_sample_secondary_positive_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (budget : CarrierSampleSecondaryChartBudget Data hd hs theta packet) :
    ∀ ell, 0 ≤ ell → ell ≤ 1 → ∀ r i (a : packet.s r i) observer k, 1 ≤ k →
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      let native := (choice.pullback (Data.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans native.chart
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
        ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Data r choice →
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ budget.forwardProfile k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ budget.inverseProfile k := by
  intro ell hell hellOne r i a observer k hk choice native t z hz hCarrier
  let piece := packet.piece r i a
  have hPreserves : Round3ParameterChartPreserves piece.native :=
    (round3_prepared_signed_native_preserves_phase Data hd hs i r _ piece).1
  let b := round3ParameterCrossNativeChart (Data.parameterChart i.2)
    (Data.parameterChart observer.2) piece.native
  have hChart : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b :=
    (round3Parameter_cross_host_conjugation (Data.parameterChart i.2)
      (Data.parameterChart observer.2) (Data.atlas.chart i.1) piece.native hPreserves).symm
  have hEval := (actual_original_native_evaluation_iff Data hd observer z).mp hz
  have hp : z.1 ∈ (Data.parameterChart observer.2).target := hd.parameter_norm_subset observer.2 hEval.2.1
  have hx : z.2 ∈ (Data.atlas.chart observer.1).target := hd.source_norm_subset observer.1 hEval.1
  have hSource : z ∈ t.source := by
    refine ⟨⟨mem_univ _,hx⟩,?_⟩
    apply (round3ParameterChartPullback_source_iff (Data.parameterChart observer.2) choice.chart
      (round3_prepared_parameter_secondary_preserves Data hd hs i r _ piece)
      (z.1,(Data.atlas.chart observer.1).symm z.2) hp).mpr
    exact packet.source r i a hCarrier
  have hOwnSample := budget.samples i
    ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2)
    (packet.parent r i a hCarrier.1)
  have hJets := repairEntrance_pointwise_original_native_observer_jets Data hd i.2 i.1 piece.native
    _ piece.slices piece.data hPreserves budget.nativeForward budget.nativeInverse
    budget.parameterTransition budget.sourceTransition budget.nativeForward_nonneg budget.nativeInverse_nonneg
    budget.parameterTransition_nonneg budget.sourceTransition_nonneg budget.transition
    (budget.forward r i a) (budget.inverse r i a) budget.parameterValue budget.sourceValue
    observer z hEval.2.1 hEval.1 hOwnSample.1 hOwnSample.2
    (budget.parameter_value observer.2 z.1 hEval.2.1) (budget.source_value observer.1 z.2 hEval.1)
  have ht : t = ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans
      (actualHostAdaptedChart (Data.atlas.chart i.1) b) := by
    dsimp only [t]
    rw [hChart]
  have hAt := hJets (ht ▸ hSource) k
  rw [← ht] at hAt
  refine ⟨?_,?_⟩
  · exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hellOne)).trans hAt.1
  · exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hellOne)).trans hAt.2

def carrierSampleSecondaryCompletionProfiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart=Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw)))
    (budget : CarrierSampleSecondaryChartBudget Data hd hs _ packet) :
    IncrementsCompletionSecondaryPacketProfiles Data hd hs _ packet where
  Tinv := budget.inverseProfile
  Kcut := budget.cutoffProfile BS TS BP TP Ds Dp
  Tobs := budget.forwardProfile
  inverse_nonneg := budget.inverseProfile_nonneg
  cutoff_nonneg := budget.cutoffProfile_nonneg BS TS BP TP Ds Dp hBS hTS hBP hTP
  observer_nonneg := budget.forwardProfile_nonneg
  positive := carrier_sample_secondary_positive_profiles Data hd hs _ packet budget
  cutoff := original_secondary_numerical_cutoff_profiles Data hd hs
    budget.mu budget.Mb budget.buffer budget.mu_pos budget.Mb_nonneg budget.buffer_pos
    BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP packet budget.literal budget.scalar

/-- The original raw parents manufacture the exact carrier samples. -/
theorem localized_parent_original_carrier_samples
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart=Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (psi : P → ℝ) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ i z, z ∈ tsupport (theta i) →
      (Data.parameterChart i.2) z.1 ∈ Data.parameterNormDomain i.2 ∧
        (Data.atlas.chart i.1) z.2 ∈ Data.sourceNormDomain i.1 := by
  intro theta i z hz
  have h := CollarCompletion.original_parameter_localized_parent_own_samples
    Data.atlas B Data.parameterSet BS TS BP TP Ds Dp RS RP
    Data.sourceNormDomain Data.parameterNormDomain hSource hParameter psi i z hz
  simpa only [hChart] using h.2.2

/-- Localized original secondary profiles on the same actual packet.
No construction domain is required to lie in K, Omega, or Q. -/
def localizedCarrierSampleSecondaryCompletionProfiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart=Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (psi : P → ℝ) (V : Set P) (hV : IsOpen V)
    (hKV : Data.parameterSet ⊆ V) (hOne : EqOn psi 1 V) :
    let theta := fun i => sourceCollarNovParameterLocalized psi
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw) i)
    ∀ (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
      (budget : CarrierSampleSecondaryChartBudget Data hd hs theta packet),
      IncrementsCompletionSecondaryPacketProfiles Data hd hs theta packet := by
  intro theta packet budget
  exact {
    Tinv := budget.inverseProfile
    Kcut := budget.cutoffProfile BS TS BP TP Ds Dp
    Tobs := budget.forwardProfile
    inverse_nonneg := budget.inverseProfile_nonneg
    cutoff_nonneg := budget.cutoffProfile_nonneg BS TS BP TP Ds Dp hBS hTS hBP hTP
    observer_nonneg := budget.forwardProfile_nonneg
    positive := carrier_sample_secondary_positive_profiles Data hd hs theta packet budget
    cutoff := localized_source_sample_secondary_cutoff_profiles Data hd hs
      budget.mu budget.Mb budget.buffer budget.mu_pos budget.Mb_nonneg budget.buffer_pos
      BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP psi V hV hKV hOne
      packet budget.literal budget.scalar }

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.carrier_sample_secondary_positive_profiles
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.carrierSampleSecondaryCompletionProfiles

#print axioms GlobalEmbedding.Continuation.OriginalIncrements.localized_parent_original_carrier_samples
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.localizedCarrierSampleSecondaryCompletionProfiles
