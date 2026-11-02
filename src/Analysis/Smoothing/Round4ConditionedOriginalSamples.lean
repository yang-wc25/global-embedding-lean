import Smoothing.Round4ConditionedObserverMeta
import Probes.Round3ParameterOriginalPrimarySamples
import Probes.ActualIncrementOriginalSampling

/-! On the actual conditioned eta support, its own inverse chart lands in
the SAME original source/parameter sampling domain. This is proved from
the unchanged raw product parent, not postulated as a chart certificate. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators ENNReal Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es

theorem round4_conditioned_primary_original_sample
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP : ℕ → ℝ) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSampling : ∀ ip, tensorLocalSamplingCoordinates B ip ⊆ Data.parameterNormDomain ip)
    (packet : Round3ParameterWholePrimaryPieceSupply Data
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw)))
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw)) packet)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (a : packet.s nu i) (y : X) :
    let piece := profiles.piece nu i a
    let own := actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native
    y ∈ piece.native.target →
    ((Data.parameterChart i.2).symm y.1,(own.symm y).2) ∈
      tsupport (round3ParameterLiftedPrimaryCutoff Data i.2 nu _ piece) →
    (Data.parameterChart i.2).symm y.1 ∈ Data.parameterSet →
    parameterTensorModelEquiv (m+1) d (piece.native.symm y) ∈
      incrementsOriginalPrimaryEvaluation Data nu i := by
  intro piece own hy hEta hK
  let x := piece.native.symm y
  let w : P × M := ((Data.parameterChart i.2).symm y.1,(own.symm y).2)
  have hHost : piece.host = i.1 := (profiles.host nu i a).trans (packet.host nu i a)
  have hPreserves := (round3Parameter_primary_native_preserves_phase Data hd i.2 nu _ piece).1
  have hpi : x.1 = y.1 := round3ParameterChartPreserves_inverse piece.native hPreserves y hy
  have heqCut : round3ParameterLiftedPrimaryCutoff Data i.2 nu _ piece =
      round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a) := by
    unfold round3ParameterLiftedPrimaryCutoff
    rw [show piece.cutoff = (packet.piece nu i a).cutoff from profiles.cutoff nu i a]
  have hParent := packet.parent nu i a (by rwa [← heqCut])
  have hOriginal := round3Parameter_product_parent_original_samples Data B hChart
    BS TS BP TP Ds Dp RS RP hSampling i w hParent
  have hOpen := (round3Parameter_originalNativeOpen_iff Data (piece.host,i.2) x).mp
    (piece.native_source (piece.native.map_target hy))
  have hXTarget : x.2 ∈ (Data.atlas.chart i.1).target := by simpa only [hHost] using hOpen.1
  have hwX : w.2 = (Data.atlas.chart i.1).symm x.2 := by
    change (Data.atlas.chart piece.host).symm x.2 = _
    rw [hHost]
  have hSource : x.2 ∈ Data.sourceNormDomain i.1 := by
    have hh := hd.source_inner_norm i.1 w.2 hOriginal.2.1
    rwa [hwX,(Data.atlas.chart i.1).right_inv hXTarget] at hh
  have hParameter : x.1 ∈ Data.parameterNormDomain i.2 := by
    have hh := hOriginal.2.2
    change (Data.parameterChart i.2) ((Data.parameterChart i.2).symm y.1) ∈ _ at hh
    rw [← hpi,(Data.parameterChart i.2).right_inv hOpen.2.1] at hh
    exact hh
  have heval := (actual_original_native_evaluation_iff Data hd i x).mpr
    ⟨hSource,hParameter,by rwa [hpi]⟩
  have hyOwn : y ∈ own.target := by rwa [piece.data.1]
  have hActive := (piece.active (own.symm y) (own.map_target hyOwn)).1
  have hJoint : incrementsOriginalJointPoint Data.atlas Data.parameterChart i
      (parameterTensorModelEquiv (m+1) d x) =
      ((Data.parameterChart i.2).symm (own.symm y).1,(own.symm y).2) := by
    rw [actual_original_jointPoint_native]
    change ((Data.parameterChart i.2).symm x.1,(Data.atlas.chart i.1).symm x.2) =
      ((Data.parameterChart i.2).symm x.1,(Data.atlas.chart piece.host).symm x.2)
    rw [hHost]
  refine ⟨heval,?_⟩
  change incrementsOriginalJointPoint Data.atlas Data.parameterChart i
    (parameterTensorModelEquiv (m+1) d x) ∈ Data.primaryDomain nu
  rwa [hJoint]

theorem round4_actual_original_conditioned_observer_meta
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP Given : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
    (hSampling : ∀ ip, tensorLocalSamplingCoordinates B ip ⊆ Data.parameterNormDomain ip)
    (packet : Round3ParameterWholePrimaryPieceSupply Data
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw)))
    (profiles : Round3ParameterWholeReferenceProfiles Data hd hs
      (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
        (tensorLocalNormalizedCutoff RP.raw)) packet)
    (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (jet : Round4PrimaryJetSupply Data i nu ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Data.parameterChart i.2)
        (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
          (tensorLocalNormalizedCutoff RP.raw) i)) (packet.s nu i) (packet.piece nu i))
    (j : ℕ) (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1) (hbuffer : ell ≤ jet.buffer)
    (hGiven : ∀ k ≤ j, parameterRound2_originalFixedPacketProfile Data k 1 ≠ ⊤)
    (hGivenBound : ∀ k ≤ j,
      (parameterRound2_originalFixedPacketProfile Data k 1).toReal ≤ Given k)
    (a : packet.s nu i) (observer : Fin Data.parameterCount) (z : X) :
    let piece := profiles.piece nu i a
    let aP := round3ParameterLiftedPrimaryChart Data i.2 nu _ piece
    let aN := round3ParameterChartPullback (Data.parameterChart observer) aP
    let etaP := round3ParameterLiftedPrimaryCutoff Data i.2 nu _ piece
    z ∈ aN.target →
    ((Data.parameterChart observer).symm z.1,(aN.symm z).2) ∈ tsupport etaP →
    (Data.parameterChart observer).symm z.1 ∈ Data.parameterSet →
    ell^j*‖iteratedFDeriv ℝ j (fun y : X =>
      etaP ((Data.parameterChart observer).symm (aN.symm y).1,(aN.symm y).2)) z‖ ≤
      round4ObserverRefinementMetaProfile (m+1) d jet.mu jet.Mb BS TS BP TP Given Ds Dp j := by
  intro piece aP aN etaP hz hEta hK
  let Bp := Data.parameterChart i.2
  let Bo := Data.parameterChart observer
  let own := actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native
  let y : X := (Bp (Bo.symm z.1),z.2)
  have ho := (round3ParameterChartPullback_target Bo aP z).mp hz
  have hp := (round3ParameterChartPullback_target Bp.symm own (Bo.symm z.1,z.2)).mp ho.2.1
  have hy : y ∈ own.target := hp.2.1
  have hyNative : y ∈ piece.native.target := by rwa [piece.data.1] at hy
  have hParam : Bo.symm z.1 ∈ Bp.source := hp.1
  have hOwnEta : (Bp.symm y.1,(own.symm y).2) ∈ tsupport etaP := by
    change (Bp.symm (Bp (Bo.symm z.1)),(own.symm y).2) ∈ tsupport etaP
    rw [Bp.left_inv hParam]
    exact hEta
  have hOwnK : Bp.symm y.1 ∈ Data.parameterSet := by
    change Bp.symm (Bp (Bo.symm z.1)) ∈ _
    rwa [Bp.left_inv hParam]
  have hSample := round4_conditioned_primary_original_sample Data hd hs BS TS BP TP Ds Dp
    B hChart RS RP hSampling packet profiles nu i a y hyNative hOwnEta hOwnK
  exact round4_actual_conditioned_observer_meta Data hd hs BS TS BP TP Given hBS hTS hBP hTP
    Ds Dp B hChart RS RP packet profiles nu i jet j ell hell hell1 hbuffer hGiven hGivenBound
    ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalPrimaryEvaluation Data nu i)
    Subset.rfl a observer z hz hEta hSample

#print axioms round4_actual_original_conditioned_observer_meta

#print axioms round4_conditioned_primary_original_sample
end GlobalEmbedding.Continuation
