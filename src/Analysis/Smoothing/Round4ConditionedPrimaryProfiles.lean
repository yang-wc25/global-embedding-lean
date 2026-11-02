import Smoothing.Round4PrimaryNamedProfiles
import Smoothing.Round4ConditionedHostProfiles
import Probes.Round3ParameterWholeReferenceProfiles

/-! The conditioned reference pieces in the actual original factory use
the SAME native functions and cutoff functions. On their real cutoff
support their positive-order forward/inverse and Meta budgets are the
explicit original-input profiles, including every mixed parameter derivative.
-/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators ENNReal
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

theorem round4_actual_conditioned_primary_named_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (BS TS BP TP Given : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Data.parameterCount) P Ep)
    (hChart : B.chart = Data.parameterChart)
    (RS : TensorRawCutoffPreparation Data.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Data.parameterSet BP TP Dp)
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
    (hGiven : parameterRound2_originalFixedPacketProfile Data j 1 ≠ ⊤)
    (hGivenBound : (parameterRound2_originalFixedPacketProfile Data j 1).toReal ≤ Given j)
    (S : Set X) (hS : S ⊆ (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalPrimaryEvaluation Data nu i)
    (a : packet.s nu i) (y : X)
    (hy : y ∈ (profiles.piece nu i a).native.target)
    (hEta : (actualHostAdaptedChart (Data.atlas.chart (profiles.piece nu i a).host)
      (profiles.piece nu i a).native).symm y ∈ tsupport (profiles.piece nu i a).cutoff)
    (hSample : (profiles.piece nu i a).native.symm y ∈ S) :
    (∀ k, 1 ≤ k → k ≤ j →
      ell^k*‖iteratedFDeriv ℝ (k+1) (profiles.piece nu i a).native
        ((profiles.piece nu i a).native.symm y)‖ ≤
        2^(j+2)*round4RefinementPhaseProfile (m+1) d Given j) ∧
    (∀ k, 1 ≤ k → k ≤ j+1 →
      ell^(k-1)*‖iteratedFDeriv ℝ k (profiles.piece nu i a).native.symm y‖ ≤
        round4RefinementInverseProfile (m+1) d jet.mu jet.Mb Given j) ∧
    ell^j*‖iteratedFDeriv ℝ j
      ((profiles.piece nu i a).cutoff ∘
        (actualHostAdaptedChart (Data.atlas.chart (profiles.piece nu i a).host)
          (profiles.piece nu i a).native).symm) y‖ ≤
      round4RefinementMetaProfile (m+1) d jet.mu jet.Mb BS TS BP TP Given Ds Dp j := by
  have hAll := jet.actual_original_profiles Data hd hs BS TS BP TP Given hBS hTS hBP hTP
    Ds Dp B hChart RS RP i nu _ _ _ j ell hell hell1 hbuffer hGiven hGivenBound S hS
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart (packet.piece nu i a).host)
  have hSource : (profiles.piece nu i a).native.source ⊆ q.target := by
    intro z hz
    have ht := actualOriginalNativeMap_source_target Data ((profiles.piece nu i a).host,i.2)
      ((profiles.piece nu i a).native_source hz).1
    rw [profiles.host] at ht
    exact ⟨mem_univ _,ht⟩
  have hEta' : (q.trans (profiles.piece nu i a).native).symm y ∈
      tsupport (profiles.piece nu i a).cutoff := by
    simpa only [actualHostAdaptedChart,profiles.host] using hEta
  have hOld := round4_conditioned_host_original_target q
    (packet.piece nu i a).native (profiles.piece nu i a).native
    (packet.piece nu i a).cutoff (profiles.piece nu i a).cutoff
    (profiles.cutoff nu i a) (profiles.forward nu i a) hSource
    (packet.piece nu i a).support y hy hEta'
  have hOldSample : (packet.piece nu i a).native.symm y ∈ S := by
    rwa [profiles.inverse] at hSample
  have hMetaEq : ((profiles.piece nu i a).cutoff ∘
      (actualHostAdaptedChart (Data.atlas.chart (profiles.piece nu i a).host)
        (profiles.piece nu i a).native).symm) =
      (packet.piece nu i a).cutoff ∘
      (actualHostAdaptedChart (Data.atlas.chart (packet.piece nu i a).host)
        (packet.piece nu i a).native).symm := by
    rw [profiles.host]
    exact round4_conditioned_host_adapted_cutoff_eq q _ _ _ _
      (profiles.cutoff nu i a) (profiles.inverse nu i a)
  refine ⟨?_,?_,?_⟩
  · intro k hk hkj
    rw [profiles.forward]
    exact hAll.1 a k hk hkj _ ⟨hOld.1,hSample⟩
  · intro k hk hkj
    rw [profiles.inverse]
    exact hAll.2.1 a k hk hkj y hOld.2 hOldSample
  · rw [hMetaEq]
    exact hAll.2.2 a y hOld.2 hOldSample

#print axioms round4_actual_conditioned_primary_named_profiles
end GlobalEmbedding.Continuation
