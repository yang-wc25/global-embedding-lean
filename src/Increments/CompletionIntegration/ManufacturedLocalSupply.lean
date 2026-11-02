import CompletionIntegration.OriginalLocalizedParents
import CompletionIntegration.ConditionedOriginalMeanPreparation
import CompletionIntegration.OriginalSecondaryPacketProfiles
import CollarCompletion.OriginalPrimaryConditioning

/-!
# Actual primary, secondary and mean suppliers from the same literal raw data

All finite geometric packets and observed profiles are constructed here.
The original charts, physical cutoffs, parameter set and norm domains are
retained. The compact-source hypothesis is explicit; no compactness of the
coordinate observation domains is requested. This is a conditional raw-data
bridge, not an assertion of the still-open finite-budget original entrance.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
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
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}


structure CompletionManufacturedLocalSupply
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (V : Set P) (R : ℕ) where
  primary : Round3ParameterWholePrimaryPieceSupply Data theta
  reference : Round3ParameterWholeReferenceProfiles Data hd hs theta primary
  secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta
  secondaryProfiles : IncrementsCompletionSecondaryPacketProfiles Data hd hs theta secondary
  Forward : ℕ → ℝ
  Inverse : ℕ → ℝ
  Meta : ℕ → ℝ
  forward_nonneg : ∀ k, 0 ≤ Forward k
  inverse_nonneg : ∀ k, 0 ≤ Inverse k
  meta_nonneg : ∀ k, 0 ≤ Meta k
  preparation :
    let conditioned := primary.replacePieces Data theta reference.piece reference.host reference.cutoff
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta conditioned
    ∀ i, FullIncrementNovOpenNativeMeanPreparation Data hd hs hn g
      (V ×ˢ (univ : Set M)) reference.cT Inverse
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+2) => Forward k))
      (fun r => round3PreparedFiniteMaximum (fun k : Fin (r+1) => Meta k))
      (R*5^Module.finrank ℝ (Ep × D)) i

variable [T2Space M] [CompactSpace M]

theorem completion_manufactured_supplies_from_literal_raw
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
    (transition : RepairOriginalTransitionBudgets Data Parameter Spatial) :
    ∃ (psi : P → ℝ) (V : Set P), IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      let theta := fun i => sourceCollarNovParameterLocalized psi
        (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
          (tensorLocalNormalizedCutoff RP.raw) i)
      (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i)) ∧
      (∀ i, IsCompact (tsupport (theta i))) ∧
      (∀ i, tsupport (theta i) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) ∧
      (∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
      Nonempty (CompletionManufacturedLocalSupply Data hd hs hn theta V ((Ds+1)*(Dp+1))) := by
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  obtain ⟨psi,V,hV,hKV,hVU,hPsi,hOne,hPsiSupport,hRange,hSmooth,hCompact,hSub,hSupport,hPart,hCount,hGerm⟩ :=
    completion_original_parameter_localized_parents BS TS BP TP hBS hTS hBP hTP Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet Data.parameterOpen
      hd.parameter_compact hd.parameter_open hd.parameter_subset RS RP
  let theta := fun i => sourceCollarNovParameterLocalized psi
    (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw) i)
  have hSupport' : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1 := by
    simpa only [hChart] using hSupport
  obtain ⟨primary⟩ := fullIncrementNov_original_open_primary_pieces Data hd hs hp
    theta hCompact hSmooth hSupport'
  obtain ⟨reference⟩ := original_localized_primary_reference_profiles Data hd hs hp hImm B
    BS TS BP TP Ds Dp RS RP psi primary
  obtain ⟨secondary⟩ := fullIncrementNov_original_open_secondary_pieces Data hd hs hp hImm
    theta hCompact hSmooth hSupport'
  obtain ⟨secondaryProfiles⟩ := completion_original_secondary_packet_profiles Data hd hs B hChart
    BS TS BP TP Ds Dp RS RP hSource hParameter Parameter Spatial hParameterNonneg
    hSpatialNonneg transition psi secondary
  obtain ⟨Forward,Inverse,Meta,hForward,hInverse,hMeta,hProfiles,hPrepared⟩ :=
    completion_conditioned_original_mean_preparation Data hd hs hn theta primary reference V hV
      hPart ((Ds+1)*(Dp+1)) hCount B hChart BS TS BP TP Ds Dp RS RP hSource hParameter
      Parameter Spatial hParameterNonneg hSpatialNonneg transition psi rfl
  exact ⟨psi,V,hV,hKV,hVU,hSmooth,hCompact,hSupport',hPart,hCount,⟨{
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
    preparation := fun i => Classical.choice (hPrepared i) }⟩⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.completion_manufactured_supplies_from_literal_raw
