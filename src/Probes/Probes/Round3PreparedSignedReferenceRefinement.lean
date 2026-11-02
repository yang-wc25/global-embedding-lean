import Probes.Round3PreparedSignedReferencePiece
import Probes.Round3PreparedInteractionRefinement
import Probes.Round3PreparedOriginalDomains

/-! The original signed phase and an actual compact parent cutoff construct
a finite family of fully prepared secondary choices. Noncritical constants,
buffer, adapted charts, ordinary cutoffs, positive reserve, true observation
samples and every later-order jet/geometry certificate are all outputs.
Good is used solely on the two-primary effective interaction carrier. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
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
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3_actual_original_signed_reference_refinement
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hParam : ∀ w ∈ W, w.1 ∈ (Data.parameterChart i.2).target)
    (hOriginal : MapsTo (fun z : Ep × M => ((Data.parameterChart i.2).symm z.1,z.2))
      W (incrementsOriginalParameterRegion Data))
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hTheta : ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ theta)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source)
    (hInner : ∀ y, y ∈ tsupport theta → y.2 ∈ Data.atlas.inner i.1) :
    ∃ (s : Finset X) (out : s → Round3PreparedSignedReferencePiece Data hd hs i r W),
      (∀ y ∈ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W,
        ∑ a : s, (out a).cutoff y = theta y) ∧
      (∀ a : s, tsupport (out a).cutoff ⊆ tsupport theta) ∧
      ∀ y, (Finset.univ.filter (fun a : s => y ∈ (out a).carrier)).card ≤ 5^Module.finrank ℝ X := by
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let pair := actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn hParam).prodMk
      continuous_snd.continuousOn
  have hPullSupport (nu : Fin Data.primaryCount) :
      incrementsGlobalRelativeSupport W (fun z => Data.cutoff nu (pull z)) ⊆
        pull ⁻¹' incrementsOriginalRelativeCutoffSupport Data nu :=
    actual_relative_support_pullback_subset W (incrementsOriginalParameterRegion Data)
      pull hPull hOriginal (Data.cutoff nu)
  have hPairPull (y : Ep × M) (hy : y ∈ pair) : pull y ∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 :=
    ⟨hPullSupport r.val.1.1 hy.1,hPullSupport r.val.1.2 hy.2⟩
  let carrier := tsupport theta ∩ pair
  have hCarrier : IsCompact carrier := actual_compact_interaction_carrier
    (tsupport theta) W hCompact (fun y hy => (hThetaSupport hy).1)
    (fun z => Data.cutoff r.val.1.1 (pull z)) (fun z => Data.cutoff r.val.1.2 (pull z))
  have hCarrierSource : carrier ⊆ q.source := fun y hy => (hThetaSupport hy.1).2
  let K := q '' carrier
  have hK : IsCompact K := hCarrier.image_of_continuousOn (q.continuousOn.mono hCarrierSource)
  let U := (q.target ∩ q.symm ⁻¹' W) ∩
    (actualOriginalPrimaryNativeOpen Data r.val.1.1 i ∩ actualOriginalPrimaryNativeOpen Data r.val.1.2 i)
  have hU : IsOpen U :=
    (q.symm.continuousOn.isOpen_inter_preimage q.open_target hW).inter
      ((actualOriginalPrimaryNativeOpen_isOpen Data hd r.val.1.1 i).inter
        (actualOriginalPrimaryNativeOpen_isOpen Data hd r.val.1.2 i))
  have hKpair : ∀ z ∈ K, ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2) ∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 := by
    rintro _ ⟨y,hy,rfl⟩
    have hh := hPairPull y hy.2
    change ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) y.2)) ∈ _
    rwa [(Data.atlas.chart i.1).left_inv (hCarrierSource hy).2]
  have hKU : K ⊆ U := by
    rintro _ ⟨y,hy,rfl⟩
    have hyW := (hThetaSupport hy.1).1
    have hyq := hCarrierSource hy
    have hpull := hKpair _ ⟨y,hy,rfl⟩
    have hprim (nu : Fin Data.primaryCount) (hsup :
        ((Data.parameterChart i.2).symm (q y).1,(Data.atlas.chart i.1).symm (q y).2) ∈
          incrementsOriginalRelativeCutoffSupport Data nu) : q y ∈ actualOriginalPrimaryNativeOpen Data nu i :=
      round3_prepared_native_primary_mem Data i nu (q y) (q.map_source hyq).2 (hParam y hyW)
        ⟨hd.cutoff_support_local nu hsup,incrementsOriginalRelativeCutoffSupport_subset Data nu hsup⟩
    exact ⟨⟨q.map_source hyq,by change q.symm (q y) ∈ W; rwa [q.left_inv hyq]⟩,
      hprim r.val.1.1 hpull.1,hprim r.val.1.2 hpull.2⟩
  obtain ⟨mu,Mb,R,buffer,O,hmu,hMb,hR,hbuffer,hO,hKO,hOU,hKR,hbufferO,hPsi,hnoncrit,hfirst,hsecond⟩ :=
    round3_actual_original_signed_phase_preparation Data hd hs hp i r K U hK hU hKU
      (fun _ hz => hz.2) hKpair
  have hRelative : incrementsGlobalRelativeSupport W theta = W ∩ tsupport theta :=
    parameterRound2_global_relativeSupport_eq W hW theta
  have hRelativeSource : incrementsGlobalRelativeSupport W theta ⊆ q.source := by
    rw [hRelative]
    exact fun _ hz => (hThetaSupport hz.2).2
  obtain ⟨s,b,e,hdata,hbO,hSourceW,hCompactEta,hSmoothEta,hSupportEta,hPartition,hCount,hNativeBound⟩ :=
    round3_actual_host_interaction_refinement mu Mb R buffer hmu hMb hbuffer
      (Data.atlas.chart i.1) (hd.atlas_smooth.chart_mem i.1) theta
      (actualOriginalParameterSignedPhase Data i r.val) W pair hW hTheta.contMDiffOn K O 0
      hRelativeSource (fun y hy => ⟨y,⟨(hRelative ▸ hy.1).2,hy.2⟩,rfl⟩)
      hO hKR (fun _ hz => (hOU hz).1.1) (fun _ hz => (hOU hz).1.2)
      hbufferO hPsi hnoncrit hfirst hsecond
  let radius := buffer/actualPhaseRefinementFactor mu Mb
  let eta := fun a : s => actualHostRefinementCutoff q theta (actualRefinementCutoff X s radius a.val)
  have hEtaTheta (a : s) : tsupport (eta a) ⊆ tsupport theta := by
    intro y hy
    exact (hRelative ▸ (hSupportEta a hy).2).2
  have hActive (a : s) (y : Ep × M) (hy : y ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) (b a)).source) :
      pull y ∈ Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
      pull y ∈ Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data := by
    have hz := (hOU (hbO a hy.2)).2
    have hnu := round3_prepared_native_primary_active Data i r.val.1.1 hz.1
    have hmu := round3_prepared_native_primary_active Data i r.val.1.2 hz.2
    change ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) y.2)) ∈ _ at hnu hmu
    rw [(Data.atlas.chart i.1).left_inv hy.1.2] at hnu hmu
    exact ⟨hnu,hmu⟩
  have hPieces (a : s) : ∃ out : Round3PreparedSignedReferencePiece Data hd hs i r W,
      out.cutoff = eta a := by
    apply round3_prepared_signed_reference_piece_from_host Data hd hs hp hImm i r (b a) (e a) (hdata a)
      (eta a) (hCompactEta a) (hSmoothEta a) (fun _ hz => (hSupportEta a hz).1)
      (fun y hy => hInner y (hEtaTheta a hy))
      (fun _ hz => round3_prepared_primary_native_subset Data i r.val.1.1 (hOU (hbO a hz)).2.1)
      (hActive a) W (hSourceW a) hParam hOriginal (2*(1+2*Mb)) (by positivity)
      (hNativeBound a)
  choose out hCutoff using hPieces
  refine ⟨s,out,?_,?_,?_⟩
  · intro y hy
    have hyW : y ∈ W := by
      obtain ⟨z,_,rfl⟩ := hy.1
      exact z.property
    simpa only [hCutoff] using hPartition y ⟨hyW,hy⟩
  · intro a
    rw [hCutoff]
    exact hEtaTheta a
  · intro y
    apply (Finset.card_le_card (show
      Finset.univ.filter (fun a : s => y ∈ (out a).carrier) ⊆
      Finset.univ.filter (fun a : s => y ∈ tsupport (eta a)) from ?_)).trans (hCount y)
    intro a ha
    have hh := (out a).carrier_eq ▸ (Finset.mem_filter.mp ha).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [hCutoff] using hh.1⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round3_actual_original_signed_reference_refinement
