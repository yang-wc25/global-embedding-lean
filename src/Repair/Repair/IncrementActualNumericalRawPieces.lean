import Probes.Round3PreparedParameterRawPieceFromHost
import Probes.Round3PreparedParameterSecondaryCurrentHost
import Repair.IncrementSecondaryChartBudget

/-! The actual fixed physical signed packet produces all canonical native
raw pieces. Inverse, cutoff and observer profiles are chosen before the new
map and scale. The current map only restricts domains while the same physical
choice functions, original samples and reference margins are retained. -/
noncomputable section
set_option backward.isDefEq.respectTransparency true
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

 theorem increment_actual_numerical_parameter_raw_pieces
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (hAll : Ref.parameterSet = univ)
    (BS TS BP TP : ℕ → ℝ)
    (hBS : ∀ j, 0 ≤ BS j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP : ∀ j, 0 ≤ BP j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (B : TensorBufferedChartFamily (Fin Ref.parameterCount) P Ep)
    (hChart : B.chart = Ref.parameterChart)
    (RS : TensorRawCutoffPreparation Ref.atlas BS TS Ds)
    (RP : TensorLocalRawPreparation B Ref.parameterSet BP TP Dp) :
    let theta := round3ParameterProductParent Ref.atlas B (squareNormalizedCutoff RS.raw)
      (tensorLocalNormalizedCutoff RP.raw)
    ∀ (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
      (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
      (charts : IncrementSecondaryChartBudget Ref hd hs theta packet),
    ∃ Tinv Kcut Tobs : ℕ → ℝ,
      Tinv = charts.inverseProfile ∧ Kcut = charts.cutoffProfile BS TS BP TP Ds Dp ∧
      Tobs = charts.forwardProfile ∧
      (∀ k, 0 ≤ Tinv k) ∧ (∀ k, 0 ≤ Kcut k) ∧ (∀ k, 0 ≤ Tobs k) ∧
      ∀ (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
      (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF)
      (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓙 x))
      (V : Set P) (normal : Fin Ref.primaryCount → P × M → Ey)
      (domain : Fin Ref.primaryCount → Set (P × M))
      (neighborhood : (p : P) → (x : M) → Set {A : LinearMap.BilinForm ℝ (TangentSpace 𝓙 x) // A.IsSymm}),
      let Data := round3ParameterStageData Ref (Function.uncurry F) H V normal domain neighborhood
      ∀ (hdNew : IncrementsOriginalDomainConditions Data) (hsNew : IncrementsOriginalSmoothInputs Data),
      IncrementsOriginalSliceImmersionInputs Data →
      ∀ r i (a : packet.s r i) observer,
      let choice := round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece
      ∃ out : Round3PreparedParameterRawPiece Data hdNew hsNew (i.1,observer) r
        ((Ref.parameterChart observer).target ×ˢ (univ : Set M))
        (fun v : Fin Ref.atlas.count => Ref.atlas.chart v)
        (fun v => (parameterTensorModelEquiv (m+1) d) ⁻¹'
          incrementsOriginalEvaluation Ref.atlas Ref.parameterChart Ref.sourceNormDomain Ref.parameterNormDomain Ref.parameterSet (v,observer)),
        out.choice = (choice.pullback (Ref.parameterChart observer)).toNative ∧
        out.Tinv = Tinv ∧ out.Kcut = Kcut ∧ out.Tobs = Tobs ∧
        out.cT = (packet.piece r i a).cT/16 ∧ out.Bnative = 1+Tobs 1 := by
  intro theta packet hSupport charts
  let Tf := charts.forwardProfile
  let Ti := charts.inverseProfile
  let Tc := charts.cutoffProfile BS TS BP TP Ds Dp
  have hTf : ∀ j, 0 ≤ Tf j := charts.forwardProfile_nonneg
  have hTi : ∀ j, 0 ≤ Ti j := charts.inverseProfile_nonneg
  have hTc : ∀ j, 0 ≤ Tc j := charts.cutoffProfile_nonneg BS TS BP TP Ds Dp hBS hTS hBP hTP
  have hProfiles := increment_actual_secondary_observer_profiles Ref hd hs theta packet hSupport
    charts.nativeForward charts.nativeInverse charts.parameterTransition charts.sourceTransition
    charts.nativeForward_nonneg charts.nativeInverse_nonneg charts.parameterTransition_nonneg charts.sourceTransition_nonneg
    charts.transition charts.forward charts.inverse charts.samples charts.parameterValue charts.sourceValue
    charts.parameter_value charts.source_value
  have hCut := increment_actual_secondary_host_cutoff_profiles Ref hd hs
    charts.mu charts.Mb charts.buffer charts.mu_pos charts.Mb_nonneg charts.buffer_pos
    BS TS BP TP hBS hTS hBP hTP Ds Dp B hChart RS RP packet charts.literal charts.scalar
  refine ⟨Ti,Tc,Tf,rfl,rfl,rfl,hTi,hTc,hTf,?_⟩
  intro F hF stable H V normal domain neighborhood Data hdNew hsNew hImm r i a observer choice
  let native := (choice.pullback (Ref.parameterChart observer)).toNative
  let W := (Ref.parameterChart observer).target ×ˢ (univ : Set M)
  let b := round3ParameterCrossNativeChart (Ref.parameterChart i.2)
    (Ref.parameterChart observer) (stable r i a).piece.native
  obtain ⟨e,hData,hNative,hInner,hChoice,hFrame⟩ :=
    round3_prepared_parameter_secondary_current_host Ref hd hs hAll i r _ (packet.piece r i a)
      F hF (stable r i a) H V normal domain neighborhood hdNew hsNew observer
  have hChart : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b :=
    congrArg ActualOriginalSecondaryChoice.chart hChoice
  have hEqual := round3_prepared_parameter_secondary_stable_functions Ref hd hs i r _
    (packet.piece r i a) F hF (stable r i a) observer
  have hRho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ choice.cutoff := by
    rw [hEqual.1]
    exact packet.smooth r i a
  have hParent : tsupport choice.cutoff ⊆ tsupport (theta i) := by
    rw [hEqual.1]
    exact packet.parent r i a
  have hPhysicalSource := (round3_prepared_parameter_secondary_carrier_source Ref hd hs i r
    (stable r i a).piece (theta i) (hSupport i) hParent).1
  have hCarrier := round3_prepared_parameter_secondary_native_carrier Data i.1 observer r choice
    (round3_prepared_parameter_secondary_preserves Ref hd hs i r _ (stable r i a).piece) hPhysicalSource
  have hCarrierSource : tsupport native.cutoff ∩ actualOriginalParameterSupportPair Data
      (i.1,observer) r.val.1.1 r.val.1.2 W ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source := by
    simpa only [hChart] using (show tsupport native.cutoff ∩ actualOriginalParameterSupportPair Data
      (i.1,observer) r.val.1.1 r.val.1.2 W ⊆ native.chart.source from hCarrier.2.1)
  have hSourceDomain : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ W := by
    simpa only [hChart] using (show native.chart.source ⊆ W from hCarrier.2.2.1)
  obtain ⟨out,hOut,hTiOut,hTcOut,hTfOut,hcTOut,hBOut⟩ :=
    round3_prepared_parameter_raw_piece_from_host Data hdNew hsNew hImm (i.1,observer) r W b e hData native.cutoff
      (round3_prepared_parameter_native_cutoff_smooth (Ref.parameterChart observer)
        (hd.parameter_charts_smooth observer) choice.cutoff hRho)
      hSourceDomain hNative hCarrierSource hInner Ti Tc Tf hTi hTc hTf (by
        intro ell hell hell1 v k z hz hy
        have hp := (hCarrier.1 (z.1,(Ref.atlas.chart v).symm z.2)).mp hy
        have hh := hProfiles F hF stable ell hell hell1 r i a (v,observer) k z hz hp.2
        have hTwo := hh.2.2
        change ell^(k-1)*‖iteratedFDeriv ℝ k
          (((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart v)).symm.trans native.chart) z‖ ≤ Tf k ∧
          ell^(k-1)*‖iteratedFDeriv ℝ k
          (((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart v)).symm.trans native.chart).symm
          ((((OpenPartialHomeomorph.refl Ep).prod (Ref.atlas.chart v)).symm.trans native.chart) z)‖ ≤ Ti k at hTwo
        rw [hChart] at hTwo
        exact hTwo)
      (fun ell hell hell1 n k hk z hz => hCut F hF stable ell hell hell1 r i a (i.1,observer) n k hk z hz)
      ((packet.piece r i a).cT/16) (div_pos (packet.piece r i a).cT_pos (by norm_num)) hFrame
  exact ⟨out,hOut.trans hChoice.symm,hTiOut,hTcOut,hTfOut,hcTOut,hBOut⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.increment_actual_numerical_parameter_raw_pieces
