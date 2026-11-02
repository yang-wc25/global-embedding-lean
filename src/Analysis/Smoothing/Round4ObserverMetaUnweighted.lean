import Smoothing.Round4ConditionedOriginalSamples

/-! A fixed positive refinement radius converts the same actual Meta estimate
into one named budget valid for every later scale in [0,1], including zero. -/
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

theorem round4_actual_original_conditioned_observer_meta_unweighted
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
    (j : ℕ) (ell : ℝ) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
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
      round4ObserverRefinementMetaProfile (m+1) d jet.mu jet.Mb BS TS BP TP Given Ds Dp j /
        (min 1 jet.buffer)^j := by
  intro piece aP aN etaP hz hEta hK
  let rho := min 1 jet.buffer
  have hrho : 0 < rho := lt_min zero_lt_one jet.buffer_pos
  have hb := round4_actual_original_conditioned_observer_meta Data hd hs BS TS BP TP Given
    hBS hTS hBP hTP Ds Dp B hChart RS RP hSampling packet profiles nu i jet j rho hrho
    (min_le_left _ _) (min_le_right _ _) hGiven hGivenBound a observer z hz hEta hK
  have hnorm : ‖iteratedFDeriv ℝ j (fun y : X =>
      etaP ((Data.parameterChart observer).symm (aN.symm y).1,(aN.symm y).2)) z‖ ≤
      round4ObserverRefinementMetaProfile (m+1) d jet.mu jet.Mb BS TS BP TP Given Ds Dp j / rho^j := by
    apply (le_div_iff₀ (pow_pos hrho j)).mpr
    simpa only [mul_comm] using hb
  exact (mul_le_of_le_one_left (norm_nonneg _) (pow_le_one₀ hell hell1)).trans hnorm

#print axioms round4_actual_original_conditioned_observer_meta_unweighted
end GlobalEmbedding.Continuation
