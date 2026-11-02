import Repair.FullIncrementNovOpenSecondarySourceModel
import IncrementsCompletion.AtScaleSecondaryRawFromHost
import Probes.Round3PreparedParameterSecondaryHostCutoffProfiles

/-! Same signed packet and true host geometry construct raw pieces from only
current-scale profiles. Choice, carrier, sample, phase, native reserve and
first-derivative budget remain literal outputs of the original constructors. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology Classical
namespace GlobalEmbedding.Continuation
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

theorem incrementsCompletion_at_scale_secondary_raw_pieces
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (ell : ℝ) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (Tinv Kcut Tobs : ℕ → ℝ)
    (hTinv : ∀ k, 0 ≤ Tinv k) (hKcut : ∀ k, 0 ≤ Kcut k) (hTobs : ∀ k, 0 ≤ Tobs k)
    (hProfiles : ∀ r i (a : packet.s r i) observer k, 1 ≤ k →
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      let native := (choice.pullback (Data.parameterChart observer.2)).toNative
      let t := ((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart observer.1)).symm.trans native.chart
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
        ((Data.parameterChart observer.2).symm z.1,(Data.atlas.chart observer.1).symm z.2) ∈
          round3PreparedParameterSecondaryCarrier Data r choice →
        ell^(k-1)*‖iteratedFDeriv ℝ k t z‖ ≤ Tobs k ∧
        ell^(k-1)*‖iteratedFDeriv ℝ k t.symm (t z)‖ ≤ Tinv k)
    (hCut : ∀ r i (a : packet.s r i) observer n k, k ≤ n →
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      ∀ z, parameterTensorModelEquiv (m+1) d z ∈ incrementsOriginalEvaluation Data.atlas Data.parameterChart
        Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet observer →
        ell^k*‖iteratedFDeriv ℝ k (fun y : X => choice.cutoff
          ((Data.parameterChart observer.2).symm y.1,(Data.atlas.chart observer.1).symm y.2)) z‖ ≤ Kcut n) :
    ∀ r i (a : packet.s r i) observer,
      let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ (packet.piece r i a)
      ∃ out : IncrementsCompletionAtScaleSecondaryRawPiece Data hd hs (i.1,observer) r
        ((Data.parameterChart observer).target ×ˢ (univ : Set M)) ell
        (fun v : Fin Data.atlas.count => Data.atlas.chart v)
        (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
          incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
            Data.parameterNormDomain Data.parameterSet (v,observer)),
        out.choice = (choice.pullback (Data.parameterChart observer)).toNative ∧
        out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧
        out.cT = (packet.piece r i a).cT ∧ out.Bnative = 1+Tobs 1 := by
  intro r i a observer choice
  let native := (choice.pullback (Data.parameterChart observer)).toNative
  let W := (Data.parameterChart observer).target ×ˢ (univ : Set M)
  let b := round3ParameterCrossNativeChart (Data.parameterChart i.2)
    (Data.parameterChart observer) (packet.piece r i a).native
  obtain ⟨e,hData,hNative,hInner,hChoice,hFrame⟩ :=
    fullIncrementNov_original_secondary_cross_host Data hd hs i r _ (packet.piece r i a) observer
  have hChart : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b :=
    congrArg ActualOriginalSecondaryChoice.chart hChoice
  have hPhysicalSource := (round3_prepared_parameter_secondary_carrier_source Data hd hs i r
    (packet.piece r i a) (theta i) (hSupport i) (packet.parent r i a)).1
  have hCarrier := round3_prepared_parameter_secondary_native_carrier Data i.1 observer r choice
    (round3_prepared_parameter_secondary_preserves Data hd hs i r _ (packet.piece r i a)) hPhysicalSource
  have hCarrierSource : tsupport native.cutoff ∩ actualOriginalParameterSupportPair Data
      (i.1,observer) r.val.1.1 r.val.1.2 W ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source := by
    simpa only [hChart] using (show tsupport native.cutoff ∩ actualOriginalParameterSupportPair Data
      (i.1,observer) r.val.1.1 r.val.1.2 W ⊆ native.chart.source from hCarrier.2.1)
  have hSourceDomain : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ W := by
    simpa only [hChart] using (show native.chart.source ⊆ W from hCarrier.2.2.1)
  obtain ⟨out,hOut,hTiOut,hTcOut,hTfOut,hcTOut,hBOut⟩ :=
    incrementsCompletion_at_scale_secondary_raw_from_host Data hd hs hImm (i.1,observer) r W b e hData native.cutoff
      (round3_prepared_parameter_native_cutoff_smooth (Data.parameterChart observer)
        (hd.parameter_charts_smooth observer) choice.cutoff (packet.smooth r i a))
      hSourceDomain hNative hCarrierSource hInner ell hell hell1 Tinv Kcut Tobs hTinv hKcut hTobs (by
        intro v k hk z hz hy
        have hp := (hCarrier.1 (z.1,(Data.atlas.chart v).symm z.2)).mp hy
        have hTwo := hProfiles r i a (v,observer) k hk z hz hp.2
        change ell^(k-1)*‖iteratedFDeriv ℝ k
          (((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart v)).symm.trans native.chart) z‖ ≤ Tobs k ∧
          ell^(k-1)*‖iteratedFDeriv ℝ k
          (((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart v)).symm.trans native.chart).symm
          ((((OpenPartialHomeomorph.refl Ep).prod (Data.atlas.chart v)).symm.trans native.chart) z)‖ ≤ Tinv k at hTwo
        rw [hChart] at hTwo
        exact hTwo)
      (fun n k hk z hz => hCut r i a (i.1,observer) n k hk z hz)
      (packet.piece r i a).cT (packet.piece r i a).cT_pos hFrame
  exact ⟨out,hOut.trans hChoice.symm,hTiOut,hTcOut,hTfOut,hcTOut,hBOut⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.incrementsCompletion_at_scale_secondary_raw_pieces
