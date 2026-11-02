import Repair.SourceCollarNovParameterLocalizedParents
import Repair.AuxBridgeNovFinitePrefixOpenPieces

/-! The actual original raw preparations now produce one open-parameter
primary packet with its own jet certificate.  No support-in-parameterOpen
assumption on the original raw functions is needed.  The one auxiliary
localization and the actual packet are chosen before all derivative orders.
The low-order phase-conditioning constants of that actual packet are still
reported as such; no uniform numerical claim for them is added here. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
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
local notation "𝓙" => 𝓘(ℝ,D)

theorem sourceCollarNov_original_parameter_localized_primary_factory
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hOmega : ∀ i, IsCompact (Data.sourceNormDomain i))
    (hQ : ∀ i, IsCompact (Data.parameterNormDomain i))
    (hSource : ∀ i, bufferedSamplingCoordinates Data.atlas i ⊆ Data.sourceNormDomain i)
    (hParameter : ∀ i, tensorLocalSamplingCoordinates B i ⊆ Data.parameterNormDomain i) :
    let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ (psi : P → ℝ) (V : Set P), IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ psi ∧ EqOn psi 1 V ∧ tsupport psi ⊆ Data.parameterOpen ∧
      (∀ p, 0 ≤ psi p ∧ psi p ≤ 1) ∧
      (∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
        (sourceCollarNovParameterLocalized psi (theta i))) ∧
      (∀ i, IsCompact (tsupport (sourceCollarNovParameterLocalized psi (theta i)))) ∧
      (∀ i, tsupport (sourceCollarNovParameterLocalized psi (theta i)) ⊆ tsupport (theta i)) ∧
      (∀ i, tsupport (sourceCollarNovParameterLocalized psi (theta i)) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) ∧
      (∀ z : P × M, z.1 ∈ V → ∑ i, sourceCollarNovParameterLocalized psi (theta i) z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i =>
        z ∈ tsupport (sourceCollarNovParameterLocalized psi (theta i)))).card ≤ (Ds+1)*(Dp+1)) ∧
      (∀ i z, z.1 ∈ Data.parameterSet →
        sourceCollarNovParameterLocalized psi (theta i) =ᶠ[𝓝 z] theta i) ∧
      ∃ packet : Round3ParameterWholePrimaryPieceSupply Data
          (fun i => sourceCollarNovParameterLocalized psi (theta i)),
        ∀ nu i, Nonempty (Round4PrimaryJetSupply Data i nu
          ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
          (round3ParameterNativeParent (Data.parameterChart i.2)
            (sourceCollarNovParameterLocalized psi (theta i)))
          (packet.s nu i) (packet.piece nu i)) := by
  intro theta
  have hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ,Ep) ∞ P := by
    rw [hChart]
    exact hd.parameter_charts_smooth
  have hQT : ∀ i, Data.parameterNormDomain i ⊆ (B.chart i).target := by
    rw [hChart]
    exact hd.parameter_norm_subset
  obtain ⟨psi,V,hV,hKV,hVU,hPsi,hOne,hPsiSupport,hRange,hSmooth,hCompact,hSub,hSupport,hPart,hCount,hGerm⟩ :=
    sourceCollarNov_actual_parameter_localized_parents BS TS BP TP hBS hTS hBP hTP Ds Dp
      Data.atlas B hd.atlas_smooth hB Data.parameterSet Data.parameterOpen
      hd.parameter_compact hd.parameter_open hd.parameter_subset RS RP
      Data.sourceNormDomain Data.parameterNormDomain hOmega hQ hd.source_norm_subset hQT hSource hParameter
  have hSupport' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (sourceCollarNovParameterLocalized psi (theta i)) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1 := by
    simpa only [hChart] using hSupport i
  obtain ⟨packet,hJets⟩ := auxBridgeNov_original_open_primary_pieces_profiles Data hd hs hp
    (fun i => sourceCollarNovParameterLocalized psi (theta i)) hCompact hSmooth hSupport'
  exact ⟨psi,V,hV,hKV,hVU,hPsi,hOne,hPsiSupport,hRange,hSmooth,hCompact,hSub,hSupport',
    hPart,hCount,hGerm,packet,hJets⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.sourceCollarNov_original_parameter_localized_primary_factory
