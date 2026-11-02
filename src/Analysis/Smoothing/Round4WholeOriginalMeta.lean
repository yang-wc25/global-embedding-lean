import Smoothing.Round4ObserverMetaUnweighted
import Probes.Round3ParameterWholePieceReplacement
import Probes.Round3ParameterNativeRefinementSamples

/-! The explicit Meta bound replaces the produced-field compact maximum in
the ORIGINAL all-observer chart-profile interface for the SAME conditioned
whole family. Forward/inverse fields and every chart, cutoff and sample stay
literal. The remaining low phase-preparation numerics are shown explicitly. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators ENNReal Classical
namespace GlobalEmbedding.Continuation

def round4WholeOriginalMetaProfile {I : Type*} [Fintype I]
    (n d : ℕ) (mu Mb buffer : I → ℝ) (BS TS BP TP Given : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  round3PreparedFiniteMaximum (fun i =>
    round4ObserverRefinementMetaProfile n d (mu i) (Mb i) BS TS BP TP Given Ds Dp j /
      (min 1 (buffer i))^j)

theorem round4WholeOriginalMetaProfile_congr_prefix {I : Type*} [Fintype I]
    (n d : ℕ) (mu Mb buffer : I → ℝ) (Ds Dp j : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ G₁ G₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ j, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j, TP₁ a = TP₂ a)
    (hG : ∀ a ≤ j, G₁ a = G₂ a) :
    round4WholeOriginalMetaProfile n d mu Mb buffer BS₁ TS₁ BP₁ TP₁ G₁ Ds Dp j =
      round4WholeOriginalMetaProfile n d mu Mb buffer BS₂ TS₂ BP₂ TP₂ G₂ Ds Dp j := by
  unfold round4WholeOriginalMetaProfile
  congr 1
  funext i
  rw [round4ObserverRefinementMetaProfile_congr_prefix n d (mu i) (Mb i) Ds Dp j
    hBS hTS hBP hTP hG]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es

theorem round4_actual_original_chart_profiles_named_meta
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hn : IncrementsOriginalFreeNormalConditions Data hd hs)
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
    (jet : ∀ nu i, Round4PrimaryJetSupply Data i nu
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
      (round3ParameterNativeParent (Data.parameterChart i.2)
        (round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
          (tensorLocalNormalizedCutoff RP.raw) i)) (packet.s nu i) (packet.piece nu i))
    (hGiven : ∀ k, parameterRound2_originalFixedPacketProfile Data k 1 ≠ ⊤)
    (hGivenBound : ∀ k, (parameterRound2_originalFixedPacketProfile Data k 1).toReal ≤ Given k)
    (Forward Inverse OldMeta : ℕ → ℝ) :
    let theta := round3ParameterProductParent Data.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    let prepared := packet.replacePieces Data theta profiles.piece profiles.host profiles.cutoff
    let g := round3ParameterWholePrimaryFamily Data hd hs hn theta prepared
    Round3ParameterOriginalChartProfiles Data g Forward Inverse OldMeta →
    Round3ParameterOriginalChartProfiles Data g Forward Inverse
      (round4WholeOriginalMetaProfile (m+1) d
        (fun v : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) => (jet v.1 v.2).mu)
        (fun v => (jet v.1 v.2).Mb) (fun v => (jet v.1 v.2).buffer)
        BS TS BP TP Given Ds Dp) := by
  intro theta prepared g hOld ell hell hell1 nu beta observer gN t etaN k z hz hEta
  have hh := hOld ell hell hell1 nu beta observer k z hz hEta
  refine ⟨hh.1,hh.2.1,hh.2.2.1,hh.2.2.2.1,?_⟩
  rcases beta with ⟨i,mu,a⟩
  by_cases hmu : mu = nu
  · subst mu
    let piece := profiles.piece nu i a
    let aP := round3ParameterLiftedPrimaryChart Data i.2 nu _ piece
    let aN := round3ParameterChartPullback (Data.parameterChart observer.2) aP
    let etaP := round3ParameterLiftedPrimaryCutoff Data i.2 nu _ piece
    have hPiece : round3ParameterWholePrimaryPiece Data hd theta prepared nu ⟨i,nu,a⟩ = piece := by
      simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece_active,
        Round3ParameterWholePrimaryPieceSupply.replacePieces,prepared,piece]
    have hNativeChart : gN.chart nu ⟨i,nu,a⟩ = aN := by
      change round3ParameterChartPullback (Data.parameterChart observer.2)
        (round3ParameterLiftedPrimaryChart Data i.2 nu _
          (round3ParameterWholePrimaryPiece Data hd theta prepared nu ⟨i,nu,a⟩)) = aN
      rw [hPiece]
    have hEtaP : g.eta nu ⟨i,nu,a⟩ = etaP := by
      change (round3ParameterWholePrimaryFamily Data hd hs hn theta prepared).eta nu ⟨i,nu,a⟩ = _
      rw [round3ParameterWholePrimaryFamily_eta,hPiece]
    have hEtaN : etaN = (fun y : X =>
        etaP ((Data.parameterChart observer.2).symm (aN.symm y).1,(aN.symm y).2)) := by
      funext y
      change g.eta nu ⟨i,nu,a⟩ ((Data.parameterChart observer.2).symm
        ((gN.chart nu ⟨i,nu,a⟩).symm y).1,((gN.chart nu ⟨i,nu,a⟩).symm y).2) = _
      rw [hEtaP,hNativeChart]
    have hSource : (z.1,(Data.atlas.chart observer.1).symm z.2) ∈
        (gN.chart nu ⟨i,nu,a⟩).source := hh.1.2
    have hInv : (gN.chart nu ⟨i,nu,a⟩).symm (t z) =
        (z.1,(Data.atlas.chart observer.1).symm z.2) :=
      (gN.chart nu ⟨i,nu,a⟩).left_inv hSource
    have hPreserves : Round3ParameterChartPreserves (gN.chart nu ⟨i,nu,a⟩) := by
      rw [hNativeChart]
      exact round3ParameterChartPullback_preserves (Data.parameterChart observer.2) aP
        (round3ParameterLiftedPrimaryChart_preserves Data i.2 nu _ piece)
    have hParam : (t z).1 = z.1 := hPreserves _ hSource
    have hTarget : t z ∈ aN.target := by rw [← hNativeChart]; exact hh.2.1.1
    have hPhysical : ((Data.parameterChart observer.2).symm (t z).1,
        (aN.symm (t z)).2) ∈ tsupport etaP := by
      rw [← hNativeChart,hInv,hParam]
      rwa [hEtaP] at hEta
    have hK : (Data.parameterChart observer.2).symm (t z).1 ∈ Data.parameterSet := by
      rw [hParam]
      exact ((actual_original_native_evaluation_iff Data hd observer z).mp hz).2.2
    have hb := round4_actual_original_conditioned_observer_meta_unweighted Data hd hs
      BS TS BP TP Given hBS hTS hBP hTP Ds Dp B hChart RS RP hSampling packet profiles nu i
      (jet nu i) k ell hell hell1 (fun l _ => hGiven l) (fun l _ => hGivenBound l)
      a observer.2 (t z) hTarget hPhysical hK
    rw [hEtaN]
    exact hb.trans (round3PreparedFiniteMaximum_bound
      (fun v : Fin Data.primaryCount × (Fin Data.atlas.count × Fin Data.parameterCount) =>
        round4ObserverRefinementMetaProfile (m+1) d (jet v.1 v.2).mu (jet v.1 v.2).Mb
          BS TS BP TP Given Ds Dp k / (min 1 (jet v.1 v.2).buffer)^k) (nu,i))
  · have hEtaZero : g.eta nu ⟨i,mu,a⟩ = 0 := by
      change (round3ParameterWholePrimaryFamily Data hd hs hn theta prepared).eta nu ⟨i,mu,a⟩ = _
      rw [round3ParameterWholePrimaryFamily_eta]
      simp only [round3ParameterWholePrimaryPiece,round3PreparedPrimarySigmaPiece,hmu,dite_false,
        round3ParameterLiftedPrimaryCutoff_empty]
    rw [hEtaZero,tsupport_zero] at hEta
    exact hEta.elim

#print axioms round4_actual_original_chart_profiles_named_meta
#print axioms round4WholeOriginalMetaProfile_congr_prefix
end GlobalEmbedding.Continuation
