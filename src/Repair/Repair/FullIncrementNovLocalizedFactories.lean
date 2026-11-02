import Repair.SourceCollarNovParameterLocalizedParentsFactory
import Repair.FullIncrementNovOpenPreparedMean
import Repair.FullIncrementNovOpenSecondaryRaw

/-! The original preparations actually produce the primary and signed
secondary packets together, on one neighborhood of the original compact
parameter set. No raw-support-in-open premise is required. Original charts,
sampling domains, raw cutoff budgets, phases, decomposition and normals are
unchanged. The all-order packets and profiles are chosen before q and scales.
Uniform numerical control of the low conditioning choices remains separate.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
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

theorem fullIncrementNov_original_localized_preparations
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
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
    let originalParent := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∃ (psi : P → ℝ) (V : Set P),
      let theta := fun i => sourceCollarNovParameterLocalized psi (originalParent i)
      IsOpen V ∧ Data.parameterSet ⊆ V ∧ V ⊆ Data.parameterOpen ∧
      ContMDiff 𝓘(ℝ,Ep) 𝓘(ℝ,ℝ) ∞ psi ∧ EqOn psi 1 V ∧
      (∀ i, tsupport (theta i) ⊆ tsupport (originalParent i)) ∧
      (∀ i, tsupport (theta i) ⊆
        ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) ∧
      (∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1) ∧
      (∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ (Ds+1)*(Dp+1)) ∧
      (∀ i z, z.1 ∈ Data.parameterSet → theta i =ᶠ[𝓝 z] originalParent i) ∧
      ∃ (packet : Round3ParameterWholePrimaryPieceSupply Data theta)
        (profiles : Round3ParameterWholeReferenceProfiles Data hd hs theta packet)
        (secondary : Round3PreparedParameterSecondaryPacket Data hd hs theta),
        ∀ nu i, Nonempty (Round4PrimaryJetSupply Data i nu
          ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
          (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
          (packet.s nu i) (packet.piece nu i)) := by
  intro originalParent
  obtain ⟨psi,V,hV,hKV,hVU,hPsi,hOne,hPsiSupport,hRange,hSmooth,hCompact,hSub,hSupport,
      hPart,hCount,hGerm,packet,hJets⟩ :=
    sourceCollarNov_original_parameter_localized_primary_factory Data hd hs hp BS TS BP TP
      hBS hTS hBP hTP Ds Dp B hChart RS RP hOmega hQ hSource hParameter
  let theta := fun i => sourceCollarNovParameterLocalized psi (originalParent i)
  have hInner (nu) (i) (a : packet.s nu i) (y : Ep × M)
      (hy : y ∈ tsupport (packet.piece nu i a).cutoff) :
      y.2 ∈ Data.atlas.inner (packet.piece nu i a).host := by
    have hyT := (packet.piece nu i a).source_domain ((packet.piece nu i a).support hy)
    have hNative := packet.native_parent nu i a hy
    have hPhys := (round3ParameterSupportedPullback_tsupport_iff
      (round3ParameterProductChart (M := M) (Data.parameterChart i.2)).symm
      (theta i) y hyT).mp hNative
    rw [packet.host nu i a]
    exact (hSupport i hPhys).2
  obtain ⟨profiles⟩ := fullIncrementNov_original_open_reference_profiles Data hd hs hp hImm
    theta packet hInner
  obtain ⟨secondary⟩ := fullIncrementNov_original_open_secondary_pieces Data hd hs hp hImm
    theta hCompact hSmooth hSupport
  refine ⟨psi,V,?_⟩
  dsimp only
  refine ⟨hV,hKV,hVU,hPsi,hOne,hSub,hSupport,hPart,hCount,hGerm,?_⟩
  exact ⟨packet,profiles,secondary,hJets⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_localized_preparations
