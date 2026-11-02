import Smoothing.Round4ConditionedPrimaryProfiles
import Smoothing.Round4PhysicalObserverEta

/-! The actual conditioned reference cutoff, lifted back to the physical
parameter manifold and viewed in ANY original observer parameter chart.
The Meta cost reads only finite original raw/fixed-packet prefixes. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Filter IsManifold
open scoped ContDiff Topology BigOperators ENNReal Classical
namespace GlobalEmbedding.Continuation

def round4ObserverRefinementMetaProfile (n d : ℕ) (mu Mb : ℝ)
    (BS TS BP TP Given : ℕ → ℝ) (Ds Dp j : ℕ) : ℝ :=
  actualFastChartTransferCost (fun k => max (TP k) 1) j *
    ∑ k ∈ Finset.range (j+1), max (round4RefinementMetaProfile n d mu Mb BS TS BP TP Given Ds Dp k) 0

theorem round4ObserverRefinementMetaProfile_nonneg
    (n d : ℕ) (mu Mb : ℝ) (BS TS BP TP Given : ℕ → ℝ) (Ds Dp j : ℕ) :
    0 ≤ round4ObserverRefinementMetaProfile n d mu Mb BS TS BP TP Given Ds Dp j := by
  exact mul_nonneg (actualFastChartTransferCost_nonneg _
    (fun k => zero_le_one.trans (le_max_right _ _)) j)
    (Finset.sum_nonneg (fun k _ => le_max_right _ _))

theorem round4ObserverRefinementMetaProfile_congr_prefix
    (n d : ℕ) (mu Mb : ℝ) (Ds Dp j : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ G₁ G₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ j, BS₁ a = BS₂ a) (hTS : ∀ a ≤ j, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ j, BP₁ a = BP₂ a) (hTP : ∀ a ≤ j, TP₁ a = TP₂ a)
    (hG : ∀ a ≤ j, G₁ a = G₂ a) :
    round4ObserverRefinementMetaProfile n d mu Mb BS₁ TS₁ BP₁ TP₁ G₁ Ds Dp j =
      round4ObserverRefinementMetaProfile n d mu Mb BS₂ TS₂ BP₂ TP₂ G₂ Ds Dp j := by
  have hFast : actualFastChartTransferCost (fun k => max (TP₁ k) 1) j =
      actualFastChartTransferCost (fun k => max (TP₂ k) 1) j := by
    unfold actualFastChartTransferCost
    rw [parameterTransitionPrefix_congr j (fun a ha => by rw [hTP a ha])]
  unfold round4ObserverRefinementMetaProfile
  rw [hFast]
  congr 1
  apply Finset.sum_congr rfl
  intro k hk
  have hkj : k ≤ j := by simpa using hk
  rw [round4RefinementMetaProfile_congr_prefix n d mu Mb Ds Dp k
    (fun a ha => hBS a (ha.trans hkj)) (fun a ha => hTS a (ha.trans hkj))
    (fun a ha => hBP a (ha.trans hkj)) (fun a ha => hTP a (ha.trans hkj)) (hG k hkj)]

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Es" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "X" => Ep × Es

theorem round4_actual_conditioned_observer_meta
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
    (hGiven : ∀ k ≤ j, parameterRound2_originalFixedPacketProfile Data k 1 ≠ ⊤)
    (hGivenBound : ∀ k ≤ j,
      (parameterRound2_originalFixedPacketProfile Data k 1).toReal ≤ Given k)
    (S : Set X) (hS : S ⊆ (parameterTensorModelEquiv (m+1) d) ⁻¹'
      incrementsOriginalPrimaryEvaluation Data nu i)
    (a : packet.s nu i) (observer : Fin Data.parameterCount) (z : X) :
    let piece := profiles.piece nu i a
    let aP := round3ParameterLiftedPrimaryChart Data i.2 nu _ piece
    let aN := round3ParameterChartPullback (Data.parameterChart observer) aP
    let etaP := round3ParameterLiftedPrimaryCutoff Data i.2 nu _ piece
    z ∈ aN.target →
    ((Data.parameterChart observer).symm z.1,(aN.symm z).2) ∈ tsupport etaP →
    piece.native.symm ((Data.parameterChart i.2) ((Data.parameterChart observer).symm z.1),z.2) ∈ S →
    ell^j*‖iteratedFDeriv ℝ j (fun y : X =>
      etaP ((Data.parameterChart observer).symm (aN.symm y).1,(aN.symm y).2)) z‖ ≤
      round4ObserverRefinementMetaProfile (m+1) d jet.mu jet.Mb BS TS BP TP Given Ds Dp j := by
  intro piece aP aN etaP hz hEta hSample
  let Bp := Data.parameterChart i.2
  let Bo := Data.parameterChart observer
  let own := actualHostAdaptedChart (Data.atlas.chart piece.host) piece.native
  let y : X := (Bp (Bo.symm z.1),z.2)
  have ha : Round3ParameterChartPreserves own := fun w hw => (piece.data.2.2.2.1 w hw).1
  have ho := (round3ParameterChartPullback_target Bo aP z).mp hz
  have hp := (round3ParameterChartPullback_target Bp.symm own (Bo.symm z.1,z.2)).mp ho.2.1
  have hy : y ∈ own.target := hp.2.1
  have hyNative : y ∈ piece.native.target := by rwa [piece.data.1] at hy
  have hParam : Bo.symm z.1 ∈ Bp.source := hp.1
  have hInv : (own.symm y).1 = y.1 := round3ParameterChartPreserves_inverse own ha y hy
  have heqP : etaP = round3ParameterLiftedPrimaryCutoff Data i.2 nu _ (packet.piece nu i a) := by
    unfold etaP round3ParameterLiftedPrimaryCutoff
    rw [show piece.cutoff = (packet.piece nu i a).cutoff from profiles.cutoff nu i a]
  have hParent := packet.parent nu i a (by rwa [← heqP])
  have hProduct := parameterLocalProductCutoff_tsupport_subset Data.atlas B
    (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw) i
    (round3ParameterProductParent_tsupport Data.atlas B _ _ i hParent)
  have hRaw : Bo.symm z.1 ∈ tsupport (RP.raw i.2) :=
    tensorLocalNormalizedCutoff_tsupport_subset RP.raw i.2 hProduct.1
  have hNativeEta : own.symm y ∈ tsupport piece.cutoff := by
    have hh := (round3ParameterSupportedPullback_tsupport_iff
      (round3ParameterProductChart (M := M) Bp) piece.cutoff
      (Bo.symm z.1,(aN.symm z).2) ⟨hParam,mem_univ _⟩).mp hEta
    have heq : (round3ParameterProductChart (M := M) Bp)
        (Bo.symm z.1,(aN.symm z).2) = own.symm y := by
      apply Prod.ext
      · exact hInv.symm
      · rfl
    rwa [heq] at hh
  have hOwnSmooth : ContDiffOn ℝ ∞ (piece.cutoff ∘ own.symm) own.target :=
    (piece.smooth.comp_contMDiffOn piece.data.2.2.1).contDiffOn
  have hC : ContDiffOn ℝ ∞ (Bp.symm.trans Bo).symm (Bp.symm.trans Bo).target :=
    contDiffOn_actualChartTransition Bo Bp (hd.parameter_charts_smooth observer)
      (hd.parameter_charts_smooth i.2)
  have hInner : ∀ k, 1 ≤ k → k ≤ j →
      ‖iteratedFDeriv ℝ k (Bp.symm.trans Bo).symm z.1‖ ≤ TP k := by
    intro k hk _
    have hh := RP.transition_jets observer i.2 k hk z.1 (by rw [hChart]; exact ho.1)
      (by rw [hChart]; exact hRaw)
    rw [hChart] at hh
    exact hh
  let Bsum := ∑ k ∈ Finset.range (j+1),
    max (round4RefinementMetaProfile (m+1) d jet.mu jet.Mb BS TS BP TP Given Ds Dp k) 0
  have hOuter : ∀ k ≤ j,
      ell^k*‖iteratedFDeriv ℝ k (piece.cutoff ∘ own.symm) y‖ ≤ Bsum := by
    intro k hkj
    have hb := (round4_actual_conditioned_primary_named_profiles Data hd hs BS TS BP TP Given
      hBS hTS hBP hTP Ds Dp B hChart RS RP packet profiles nu i jet k ell hell hell1 hbuffer
      (hGiven k hkj) (hGivenBound k hkj) S hS a y hyNative hNativeEta hSample).2.2
    exact hb.trans ((le_max_left _ _).trans (Finset.single_le_sum
      (fun l _ => le_max_right _ _) (by simpa using hkj)))
  have hb := round4_physical_observer_eta_slow_jet Bp Bo hC own ha piece.cutoff hOwnSmooth
    TP j ell Bsum hell hell1 z hz hOuter hInner
  have hEtaEq : etaP = (fun w : P × M =>
      if w.1 ∈ Bp.source then piece.cutoff (Bp w.1,w.2) else 0) :=
    funext (round3ParameterLiftedPrimaryCutoff_eq Data i.2 nu _ piece)
  rw [hEtaEq]
  exact hb

#print axioms round4_actual_conditioned_observer_meta
#print axioms round4ObserverRefinementMetaProfile_congr_prefix
end GlobalEmbedding.Continuation
