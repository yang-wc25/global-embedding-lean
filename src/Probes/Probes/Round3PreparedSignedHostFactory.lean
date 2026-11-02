import Probes.Round3PreparedSignedPiece

/-! A genuine original signed phase produces one prepared choice and every
later-order certificate. Only the actual original data, compact cutoff and
true source/observation sets are inputs. Geometry, inverse/cutoff/observer
profiles and all solver records are constructed inside this theorem. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold
open scoped ContDiff Topology BigOperators Classical ENNReal
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_prepared_signed_piece_from_host
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (b : OpenPartialHomeomorph X X) (e : Ep → OpenPartialHomeomorph M D)
    (hdata : ActualOriginalHostSliceData (Data.atlas.chart i.1) b
      (actualOriginalParameterSignedPhase Data i r.val) e)
    (rho : Ep × M → ℝ) (hCompact : IsCompact (tsupport rho))
    (hRho : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ rho)
    (hSupport : tsupport rho ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source)
    (hsource : b.source ⊆ actualOriginalNativeOpen Data i)
    (hactive : ∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
      ((Data.parameterChart i.2).symm w.1,w.2) ∈
        Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data)
    (W : Set (Ep × M))
    (hW : (actualHostAdaptedChart (Data.atlas.chart i.1) b).source ⊆ W)
    (hParam : ∀ w ∈ W, w.1 ∈ (Data.parameterChart i.2).target)
    (hOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2))
      W (incrementsOriginalParameterRegion Data))
    (Bnative : ℝ) (hBnative : 0 < Bnative)
    (hnative : ∀ z ∈ b.source, ‖fderiv ℝ b z‖ ≤ Bnative)
    (K : Set (Ep × M)) (hK : IsCompact K)
    {Index : Type*} [Fintype Index]
    (observer : Index → OpenPartialHomeomorph M D)
    (hObserver : ∀ v, observer v ∈ IsManifold.maximalAtlas 𝓙 ∞ M)
    (Samples : Index → Set X) (hSamples : ∀ v, IsCompact (Samples v))
    (hTarget : ∀ v, Samples v ⊆ (actualOriginalHostJointChart («Ep» := Ep) (observer v)).target)
    (hPhysical : ∀ v, MapsTo (fun z : X => (z.1,(observer v).symm z.2)) (Samples v) K)
    (hNative : MapsTo (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1))
      (K ∩ tsupport rho) ((parameterTensorModelEquiv (m+1) d) ⁻¹'
        incrementsOriginalEvaluation Data.atlas Data.parameterChart Data.sourceNormDomain
          Data.parameterNormDomain Data.parameterSet i)) :
    ∃ out : Round3PreparedSignedPiece Data hd hs i r W observer Samples,
      out.choice.cutoff = rho := by
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  let carrier := tsupport rho ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn hParam).prodMk
      continuous_snd.continuousOn
  have hOriginalSupport (nu : Fin Data.primaryCount) :
      incrementsGlobalRelativeSupport W (fun z => Data.cutoff nu (pull z)) ⊆
        pull ⁻¹' incrementsOriginalRelativeCutoffSupport Data nu :=
    actual_relative_support_pullback_subset W (incrementsOriginalParameterRegion Data)
      pull hPull hOriginal (Data.cutoff nu)
  have hCarrierCompact : IsCompact carrier :=
    actual_compact_interaction_carrier (tsupport rho) W hCompact (hSupport.trans hW)
      (fun z => Data.cutoff r.val.1.1 (pull z)) (fun z => Data.cutoff r.val.1.2 (pull z))
  have hCarrierSource : carrier ⊆ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source :=
    inter_subset_left.trans hSupport
  have hPair : ∀ w ∈ carrier, pull w ∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 :=
    fun w hw => ⟨hOriginalSupport r.val.1.1 hw.2.1,hOriginalSupport r.val.1.2 hw.2.2⟩
  have hCarrierClosed : IsClosed (Subtype.val ⁻¹' carrier : Set W) :=
    ((isClosed_tsupport rho).preimage continuous_subtype_val).inter
      ((actual_relative_support_preimage_closed W (fun z => Data.cutoff r.val.1.1 (pull z))).inter
        (actual_relative_support_preimage_closed W (fun z => Data.cutoff r.val.1.2 (pull z))))
  obtain ⟨cF,cT,b',e',hcF,hcT,hSource,hTarget',hb,hbi,hdata',hSupport',hASource,hInverse,hFb,hTb⟩ :=
    actual_original_signed_carrier_conditioned_chart Data hd hs hp hImm i r b e hdata
      carrier hCarrierCompact hCarrierSource hsource hactive hPair
  let a := actualHostAdaptedChart (Data.atlas.chart i.1) b'
  let choice : ActualOriginalSecondaryChoice Ep M m :=
    ⟨Data.atlas.chart i.1,a,(fun p x => (e' p).symm x),rho⟩
  let S := a '' (K ∩ carrier)
  obtain ⟨Tinv,Kcut,Tobs,hTinv,hKcut,hTobs,hScompact,hSb,hSample,hHostSample,hObsSample,
      hCutSmooth,hInvSmooth,hJets⟩ :=
    round3_prepared_host_samples_and_profiles (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1)
      b' (actualOriginalParameterSignedPhase Data i r.val) e' hdata' rho hRho carrier K
      hCarrierCompact hK hSupport' observer hObserver Samples hSamples hTarget hPhysical
      ((parameterTensorModelEquiv (m+1) d) ⁻¹' incrementsOriginalEvaluation Data.atlas
        Data.parameterChart Data.sourceNormDomain Data.parameterNormDomain Data.parameterSet i)
      (fun z hz => hNative ⟨hz.1,hz.2.1⟩)
  have hRelativeSupport : tsupport (fun y : W => rho y.val) ⊆
      Subtype.val ⁻¹' tsupport rho := by
    apply closure_minimal _ ((isClosed_tsupport rho).preimage continuous_subtype_val)
    intro y hy
    exact subset_tsupport rho hy
  let out : Round3PreparedSignedPiece Data hd hs i r W observer Samples := {
    choice := choice
    carrier := carrier
    sample := S
    host_eq := rfl
    cutoff_smooth := hRho
    carrier_eq := rfl
    sample_subset := by rw [hdata'.1]; exact hSb
    carrier_source := hSupport'
    source_domain := hASource.trans hW
    chart_smooth := hdata'.2.1
    chart_inverse_smooth := hdata'.2.2.1
    host_source := fun _ hz => hz.1
    support := fun _ hz => ⟨hRelativeSupport hz.1,hz.2⟩
    pair := inter_subset_right
    cut_smooth := hCutSmooth
    inv_smooth := hInvSmooth
    host_samples := hHostSample
    observer_samples := hObsSample
    Tinv := Tinv
    Kcut := Kcut
    Tobs := Tobs
    Tinv_nonneg := hTinv
    Kcut_nonneg := hKcut
    Tobs_nonneg := hTobs
    cut_jets := fun ell hell hell1 => (hJets ell hell hell1).2.2.1
    inv_jets := fun ell hell hell1 => (hJets ell hell hell1).2.1
    observer_jets := fun ell hell hell1 => (hJets ell hell hell1).2.2.2
    cT := cT
    Bnative := Bnative
    cT_pos := hcT
    Bnative_pos := hBnative
    produce := by
      intro n j ell budget c hell hell1 hEll hfinite hbudget
      obtain ⟨geom,hc,hchart,hphase,hsample,hsupport,_⟩ :=
        actual_secondary_geometry_from_constructed_host Data hd hs hImm i r.val.1.1
          b' e' (actualOriginalParameterSignedPhase Data i r.val) hdata' carrier W
          hCarrierClosed hSupport' (hASource.trans hW) (hSource.trans hsource)
          n j Tinv hTinv S hSb hSample ell budget c cT Bnative hell hell1 hEll hcT hBnative
          hfinite hbudget (fun z hz => by rw [hb]; exact hnative z (hSource hz)) hTb
          (fun k _ _ z hz => (hJets ell hell.le hell1).1 k z hz)
      exact ⟨geom,hc,hchart,hphase,hsample,hsupport⟩ }
  exact ⟨out,rfl⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_prepared_signed_piece_from_host
