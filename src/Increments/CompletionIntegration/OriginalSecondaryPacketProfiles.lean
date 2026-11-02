import CompletionIntegration.PreparedSecondaryObserverCutoffs
import CollarCompletion.OriginalSecondaryPositiveProfiles

/-!
# Both actual secondary profile fields are manufactured internally

The actual original raw preparations fix the literal localized parent.
The fixed actual packet manufactures its native chart profiles and its
compact physical cutoff profiles. The original transition budgets transport
these profiles on the unchanged original samples. No output profile, whole
chart inclusion in Q, compact observation domain, or coordinate-value bound
is an input. The upstream construction of the original raw preparations and
uniform finite-budget bounds for adapted pieces remains a distinct obligation.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
open CollarCompletion
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem completion_original_secondary_packet_profiles
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
      Nonempty (IncrementsCompletionSecondaryPacketProfiles Data hd hs theta packet) := by
  intro theta packet
  obtain ⟨Tinv,Tobs,hInv,hObs,hPositive⟩ := original_secondary_packet_positive_profiles
    Data hd hs B hChart BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial
      hParameterNonneg hSpatialNonneg transition psi packet
  have hSupport : ∀ i, tsupport (theta i) ⊆
      (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1 := by
    intro i z hz
    have h := original_parameter_localized_parent_inner Data.atlas B Data.parameterSet
      BS TS BP TP Ds Dp RS RP psi i hz
    have hp := B.inner_subset i.2 h.1
    rw [hChart] at hp
    exact ⟨hp,h.2⟩
  obtain ⟨Kcut,hCut,hCutoff⟩ := prepared_secondary_original_observer_cutoff_profiles
    Data hd hs theta packet hSupport Parameter Spatial hParameterNonneg hSpatialNonneg transition
  exact ⟨{
    Tinv := Tinv
    Kcut := Kcut
    Tobs := Tobs
    inverse_nonneg := hInv
    cutoff_nonneg := hCut
    observer_nonneg := hObs
    positive := hPositive
    cutoff := hCutoff }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.completion_original_secondary_packet_profiles
