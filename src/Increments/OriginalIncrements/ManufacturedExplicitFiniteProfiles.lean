import OriginalIncrements.OriginalFiniteLowPrimarySupply
import OriginalIncrements.ExplicitPrimaryAdaptedProfiles
import OriginalIncrements.ExplicitProfileMeanPreparation
import OriginalCollars.ConditionedOriginalCutoffBudget
import OriginalIncrements.OriginalLowBudgetLocalization
import OriginalIncrements.OriginalCurrentScaleMeta
import CompletionIntegration.ManufacturedLocalSupply

/-!
# Actual original finite profiles are the profiles used by the mean threshold

The original two-entry phase data manufacture the actual parameter cutoff
and primary packet. The named original-input observer costs supply Forward
and Inverse; the exact raw-parent/grid observer cutoff cost supplies Meta
through the actual inverse. The actual mean preparation is reconstructed
with these values, rather than retaining unrelated compact derivative maxima.

Every equality in the output binds these numerical profiles to the same
packet used by the finite mean and final displacement. The selected spatial
margin, buffer and transverse reserve remain actual fixed-decomposition
geometric data, not an assertion of arbitrary-atlas class uniformity.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion OriginalCollars
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}


variable [T2Space M] [CompactSpace M]

theorem manufactured_literal_raw_supplies_with_explicit_finite_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (Parameter Spatial : ℕ → ℝ)
    (hParameterNonneg : ∀ k, 0 ≤ Parameter k) (hSpatialNonneg : ∀ k, 0 ≤ Spatial k)
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial)
    (hFinite : ∀ k, actualOriginalGivenInputProfile Data k 1 ≠ ⊤) :
    ∃ (psi : P → ℝ) (V : Set P), IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      EqOn psi 1 V ∧
      let theta := fun i => sourceCollarNovParameterLocalized psi
        (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
          (tensorLocalNormalizedCutoff RP.raw) i)
      (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
      (∀ i, IsCompact (tsupport (theta i))) ∧
      (∀ i, tsupport (theta i) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) ∧
      (∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
      ∃ (budgeted : OriginalBudgetedPrimarySupply Data theta)
        (supply : CompletionManufacturedLocalSupply Data hd hs hn theta V ((Ds+1)*(Dp+1))),
        supply.primary = budgeted.packet ∧
        (∀ nu i, budgeted.Mb nu i = originalLowPhaseBudget m d
          (fun k => (actualOriginalGivenInputProfile Data k 1).toReal)) ∧
        (∀ nu i, budgeted.buffer nu i ≤ 1) ∧
        OriginalCurrentScaleMetaCertificate Data theta BS TS BP TP Ds Dp budgeted ∧
        supply.Forward = originalBudgetedObserverForward Data theta budgeted
          (fun k => (actualOriginalGivenInputProfile Data k 1).toReal) Parameter Spatial ∧
        supply.Inverse = originalBudgetedObserverInverse Data theta budgeted
          (fun k => (actualOriginalGivenInputProfile Data k 1).toReal) Parameter Spatial ∧
        supply.Meta = repairEntranceCompositionProfile
          (originalObserverCutoffProfile Data theta budgeted BS TS BP TP Parameter Spatial Ds Dp)
          (originalBudgetedObserverInverse Data theta budgeted
            (fun k => (actualOriginalGivenInputProfile Data k 1).toReal) Parameter Spatial) := by
  let Packet := fun k => (actualOriginalGivenInputProfile Data k 1).toReal
  obtain ⟨psi,V,hV,hKV,hVU,hOne,hSmooth,hCompact,hSupport,hPart,hCount,hLow⟩ :=
    original_parameter_localization_with_finite_phase_budget Data hd hs B hChart
      BS TS BP TP hBS hTS hBP hTP Ds Dp RS RP hSource hParameter 1 zero_lt_one Packet
      (fun k _ => hFinite k) (fun _ _ => le_rfl)
  let theta := fun i => sourceCollarNovParameterLocalized psi
    (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i)
  obtain ⟨budgeted,hMbEq,hBufferLe⟩ := original_open_primary_supply_from_finite_low_phase_budget
    Data hd hs hp theta hCompact hSmooth hSupport 1 zero_lt_one Packet hLow
  let primary := budgeted.packet
  obtain ⟨reference⟩ := original_localized_primary_reference_profiles Data hd hs hp hImm B
    BS TS BP TP Ds Dp RS RP psi primary
  obtain ⟨secondary⟩ := fullIncrementNov_original_open_secondary_pieces Data hd hs hp hImm
    theta hCompact hSmooth hSupport
  obtain ⟨secondaryProfiles⟩ := completion_original_secondary_packet_profiles Data hd hs B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial hParameterNonneg
    hSpatialNonneg transition psi secondary
  let Forward := originalBudgetedObserverForward Data theta budgeted Packet Parameter Spatial
  let Inverse := originalBudgetedObserverInverse Data theta budgeted Packet Parameter Spatial
  let Cutoff := originalObserverCutoffProfile Data theta budgeted BS TS BP TP Parameter Spatial Ds Dp
  let Meta := repairEntranceCompositionProfile Cutoff Inverse
  have hForward : ∀ k, 0 ≤ Forward k :=
    originalBudgetedObserverForward_nonneg Data theta budgeted Packet Parameter Spatial
  have hInverse : ∀ k, 0 ≤ Inverse k :=
    originalBudgetedObserverInverse_nonneg Data theta budgeted Packet Parameter Spatial
  have hCutoff : ∀ k, 0 ≤ Cutoff k :=
    originalObserverCutoffProfile_nonneg Data theta budgeted BS TS BP TP Parameter Spatial Ds Dp
  have hMeta : ∀ k, 0 ≤ Meta k := repairEntranceCompositionProfile_nonneg Cutoff Inverse hCutoff hInverse
  have hProfiles := original_primary_profiles_from_explicit_cutoff_bound Data hd hs hn B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial hParameterNonneg hSpatialNonneg
    transition Packet hFinite (fun _ => le_rfl) psi budgeted reference Cutoff hCutoff
    (conditioned_original_observer_cutoff_budget Data hd hs hn BS TS BP TP hBS hTS hBP hTP Ds Dp
      B hChart RS RP psi V hV hKV hOne Parameter Spatial hParameterNonneg hSpatialNonneg transition
      budgeted hCompact hSmooth reference)
  have hPrepared := original_conditioned_mean_preparation_from_proved_profiles Data hd hs hn theta
    primary reference V hV hPart ((Ds+1)*(Dp+1)) hCount Forward Inverse Meta hProfiles
  refine ⟨psi,V,hV,hKV,hVU,hOne,hSmooth,hCompact,hSupport,hPart,hCount,budgeted,{
    primary := primary
    reference := reference
    secondary := secondary
    secondaryProfiles := secondaryProfiles
    Forward := Forward
    Inverse := Inverse
    Meta := Meta
    forward_nonneg := hForward
    inverse_nonneg := hInverse
    meta_nonneg := hMeta
    preparation := fun i => Classical.choice (hPrepared i) },rfl,hMbEq,hBufferLe,?_,rfl,rfl,rfl⟩
  intro Given nu i a j ell hell hell1 hGiven hGivenBound y hy hSample
  exact original_primary_cutoff_current_scale_profile Data hd hs BS TS BP TP Given hBS hTS hBP hTP
    Ds Dp B hChart RS RP psi V hV hKV hOne budgeted hCompact hSmooth nu i a j ell
    hell hell1 hGiven hGivenBound y hy hSample


end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.manufactured_literal_raw_supplies_with_explicit_finite_profiles
