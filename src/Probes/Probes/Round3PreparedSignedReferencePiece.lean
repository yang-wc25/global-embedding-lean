import Probes.Round3PreparedReferenceHostTarget
import Probes.Round3PreparedSignedPiece

/-! A fixed signed/doubled reference piece. Its choice, genuine compact
carrier, first/transverse reserves, ordinary Hessian bound, and whole-domain
chart profiles are all produced from the original reference data. -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)
private local instance signedFirstNormed : NormedAddCommGroup (D →L[ℝ] Ey) := inferInstance
private local instance signedFirstSpace : NormedSpace ℝ (D →L[ℝ] Ey) := inferInstance
private local instance signedHessianNormed : NormedAddCommGroup (D →L[ℝ] D →L[ℝ] Ey) := inferInstance
private local instance signedHessianSpace : NormedSpace ℝ (D →L[ℝ] D →L[ℝ] Ey) := inferInstance

structure Round3PreparedSignedReferencePiece
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M)) where
  native : OpenPartialHomeomorph X X
  slices : Ep → OpenPartialHomeomorph M D
  cutoff : Ep × M → ℝ
  carrier : Set (Ep × M)
  data : ActualOriginalHostSliceData (Data.atlas.chart i.1) native (actualOriginalParameterSignedPhase Data i r.val) slices
  native_source : native.source ⊆ actualOriginalNativeOpen Data i
  source_domain : (actualHostAdaptedChart (Data.atlas.chart i.1) native).source ⊆ W
  active : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) native).source,
    ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
    ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data
  source_inner : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) native).source, w.2 ∈ Data.atlas.inner i.1
  cutoff_compact : IsCompact (tsupport cutoff)
  cutoff_smooth : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ cutoff
  carrier_eq : carrier = tsupport cutoff ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  carrier_compact : IsCompact carrier
  carrier_source : carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) native).source
  cF : ℝ
  cT : ℝ
  MH : ℝ
  Bnative : ℝ
  cF_pos : 0 < cF
  cT_pos : 0 < cT
  MH_nonneg : 0 ≤ MH
  Bnative_pos : 0 < Bnative
  native_first : ∀ z ∈ native.source, ‖fderiv ℝ native z‖ ≤ Bnative
  first : ∀ z ∈ native.target, ∀ v : D,
    cF*‖v‖^2 ≤ ‖fderiv ℝ (actualOriginalOpenParameterSlice Data i z.1 ∘ (slices z.1).symm) z.2 v‖^2
  transverse : ∀ z ∈ native.target, ∀ v : Tdata,
    cT*‖v‖^2 ≤ ‖incrementsModeAmbientTransverseFrame (actualOriginalOpenParameterSlice Data i z.1)
      (actualOriginalOpenParameterSlice_contMDiff Data hd hs i z.1) (slices z.1).symm z.2 v‖^2
  hessian : ∀ z ∈ native.target,
    ‖fderiv ℝ (fderiv ℝ (actualOriginalOpenParameterSlice Data i z.1 ∘ (slices z.1).symm)) z.2‖ ≤ MH
  Tinv : ℕ → ℝ
  Forward : ℕ → ℝ
  Tinv_nonneg : ∀ j, 0 ≤ Tinv j
  Forward_nonneg : ∀ j, 0 ≤ Forward j
  inverse_jets : ∀ j z, z ∈ native.target → ‖iteratedFDeriv ℝ j native.symm z‖ ≤ Tinv j
  forward_jets : ∀ j z, z ∈ native.source → ‖iteratedFDeriv ℝ j native z‖ ≤ Forward j

variable [T2Space M]

theorem round3_prepared_signed_reference_piece_from_host
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs) (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b (actualOriginalParameterSignedPhase Data i r.val) e)
    (rho : Ep × M → ℝ) (hCompact : IsCompact (tsupport rho))
    (hRho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho)
    (hSupport : tsupport rho ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hInner : ∀ y, y ∈ tsupport rho → y.2 ∈ Data.atlas.inner i.1)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hactive : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
      ((Data.parameterChart i.2).symm w.1,w.2) ∈ Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data)
    (W : Set (Ep × M)) (hW : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ W)
    (hParam : ∀ w ∈ W, w.1 ∈ (Data.parameterChart i.2).target)
    (hOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2)) W (incrementsOriginalParameterRegion Data))
    (Bnative : ℝ) (hBnative : 0 < Bnative) (hnative : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ Bnative) :
    ∃ out : Round3PreparedSignedReferencePiece Data hd hs i r W, out.cutoff = rho := by
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  let carrier := tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn hParam).prodMk continuous_snd.continuousOn
  have hOriginalSupport (nu : Fin Data.primaryCount) : incrementsGlobalRelativeSupport W
      (fun z => Data.cutoff nu (pull z)) ⊆ pull ⁻¹' incrementsOriginalRelativeCutoffSupport Data nu :=
    actual_relative_support_pullback_subset W (incrementsOriginalParameterRegion Data) pull hPull hOriginal (Data.cutoff nu)
  have hCarrierCompact : IsCompact carrier := actual_compact_interaction_carrier (tsupport rho) W hCompact
    (hSupport.trans hW) (fun z => Data.cutoff r.val.1.1 (pull z)) (fun z => Data.cutoff r.val.1.2 (pull z))
  have hCarrierSource : carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source := inter_subset_left.trans hSupport
  have hPair : ∀ w ∈ carrier, pull w ∈ incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
      incrementsOriginalRelativeCutoffSupport Data r.val.1.2 :=
    fun w hw => ⟨hOriginalSupport r.val.1.1 hw.2.1,hOriginalSupport r.val.1.2 hw.2.2⟩
  obtain ⟨cF,cT,b0,e0,hcF,hcT,hSource0,hTarget0,hb0,hbi0,hData0,hCarrier0,hASource0,hSlices0,hFirst0,hFrame0⟩ :=
    actual_original_signed_carrier_conditioned_chart Data hd hs hp hImm i r b e hdata
      carrier hCarrierCompact hCarrierSource hsource hactive hPair
  have hFjoint : ContMDiffOn ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,Ey) ∞
      (Function.uncurry (actualOriginalOpenParameterSlice Data i)) W := by
    have hh := actual_original_parameter_pullback_smooth Data hd i.2 Data.F
      (incrementsOriginalParameterRegion Data) hs.F_joint W hParam hOriginal
    apply hh.congr
    intro z hz
    change actualOriginalOpenParameterSlice Data i z.1 z.2 = _
    rw [actualOriginalOpenParameterSlice_eq Data i z.1 (hOriginal hz).1]
    rfl
  obtain ⟨MH,Ti,Tf,b1,e1,hMH,hTi,hTf,hData1,hSource1,hTarget1,hb1,hbi1,hSlices1,hCarrier1,hASource1,hInner1,hHessian,hInv,hForw⟩ :=
    round3_prepared_reference_host_target (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
      b0 (actualOriginalParameterSignedPhase Data i r.val) e0 hData0 carrier W hCarrierCompact hCarrier0
      (hASource0.trans hW) (Data.atlas.inner i.1) (Data.atlas.inner_open i.1)
      (fun y hy => hInner y hy.1) (actualOriginalOpenParameterSlice Data i) hFjoint
  refine ⟨{
    native := b1
    slices := e1
    cutoff := rho
    carrier := carrier
    data := hData1
    native_source := hSource1.trans (hSource0.trans hsource)
    source_domain := hASource1.trans (hASource0.trans hW)
    active := fun w hw => hactive w (hASource0 (hASource1 hw))
    source_inner := hInner1
    cutoff_compact := hCompact
    cutoff_smooth := hRho
    carrier_eq := rfl
    carrier_compact := hCarrierCompact
    carrier_source := hCarrier1
    cF := cF
    cT := cT
    MH := MH
    Bnative := Bnative
    cF_pos := hcF
    cT_pos := hcT
    MH_nonneg := hMH
    Bnative_pos := hBnative
    native_first := ?_
    first := ?_
    transverse := ?_
    hessian := hHessian
    Tinv := Ti
    Forward := Tf
    Tinv_nonneg := hTi
    Forward_nonneg := hTf
    inverse_jets := hInv
    forward_jets := hForw },rfl⟩
  · intro z hz
    rw [hb1,hb0]
    exact hnative z (hSource0 (hSource1 hz))
  · intro z hz v
    rw [hSlices1]
    exact hFirst0 z (hTarget1 hz) v
  · intro z hz v
    rw [hSlices1]
    exact hFrame0 z (hTarget1 hz) v

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_signed_reference_piece_from_host
