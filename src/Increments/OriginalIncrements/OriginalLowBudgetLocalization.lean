import OriginalIncrements.OriginalPhaseParameterNeighborhood
import CompletionIntegration.ManufacturedLocalSupply

/-!
# Manufacture the actual parameter cutoff inside the finite-input neighborhood

The finite original phase budget first selects one open neighborhood by
continuity on the original samples. The actual smooth parameter cutoff is
then constructed with support inside that neighborhood. Its literal raw
product parents retain the original compact support, partition, degree bound
and all-order germ equality at the original parameter samples. The selected
first/two-jet phase bound holds on their entire active compact carrier.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
open CollarCompletion
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)
variable [CompactSpace M]

theorem original_parameter_localization_with_finite_phase_budget
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i)
    (ell : ℝ) (hell : 0 < ell) (Packet : ℕ → ℝ)
    (hFinite : ∀ k ≤ 1, actualOriginalGivenInputProfile Data k ell ≠ ⊤)
    (hBudget : ∀ k ≤ 1, (actualOriginalGivenInputProfile Data k ell).toReal ≤ Packet k) :
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
      ∀ (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
        (k : ℕ), k ≤ 1 → ∀ z : P × M,
        z ∈ tsupport (theta i) → z ∈ incrementsOriginalRelativeCutoffSupport Data nu →
        originalPhaseJetAtPhysical Data nu i k ell z <
          actualOriginalTotalPhaseJetCost (m+1) d k*Packet k+1 := by
  obtain ⟨W,hW,hKW,hWU,hLow⟩ := original_phase_low_jets_parameter_neighborhood Data hd hs
    B hChart BS TS BP TP Ds Dp RS RP hSource hParameter ell hell Packet hFinite hBudget
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  obtain ⟨psi,V,hV,hKV,hVW,hPsi,hOne,hPsiSupport,hRange,hSmooth,hCompact,hSub,hSupport,hPart,hCount,hGerm⟩ :=
    completion_original_parameter_localized_parents BS TS BP TP hBS hTS hBP hTP Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet W hd.parameter_compact hW hKW RS RP
  refine ⟨psi,V,hV,hKV,hVW.trans hWU,hOne,hSmooth,hCompact,?_,hPart,hCount,?_⟩
  · intro i z hz
    have hi := hSupport i hz
    exact ⟨⟨by simpa only [hChart] using hi.1.1,hWU hi.1.2⟩,hi.2⟩
  · intro nu i k hk z hz hcutoff
    exact hLow nu i k hk z (hSupport i hz).1.2
      (sourceCollarNov_parameter_localized_tsupport psi _ hz).1 hcutoff

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_parameter_localization_with_finite_phase_budget
