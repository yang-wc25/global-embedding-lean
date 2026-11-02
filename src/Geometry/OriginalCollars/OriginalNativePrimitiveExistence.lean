import OriginalIncrements.OriginalSignedCompactReserves
import OriginalCollars.CompactPrimitiveBudgets
import OriginalCollars.NativePrimitiveSignedRegion
import Probes.Round3PreparedSignedReferenceRefinement

/-! Actual fixed-data primitive geometry is manufactured from the original
compact parent, original signed Good condition, and original immersion.
The original parameter set and observation domains retain their exact
scope: no open construction set is required to lie in them. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold Metric
open scoped ContDiff Topology TensorProduct Classical
namespace GlobalEmbedding.Continuation.OriginalIncrements
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [T2Space M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "V" => EuclideanSpace ℝ (Fin N)
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

private theorem original_signed_carrier_neighborhood
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hParam : ∀w∈W, w.1∈(Data.parameterChart i.2).target)
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hOriginal : ∀y∈tsupport theta,
      ((Data.parameterChart i.2).symm y.1,y.2)∈incrementsOriginalParameterRegion Data)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source)
    (hInner : ∀y∈tsupport theta, y.2∈Data.atlas.inner i.1) :
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
    let K := q '' (tsupport theta ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W)
    IsCompact K ∧ ∃U : Set X, IsOpen U ∧ K⊆U ∧ U⊆q.target ∧ MapsTo q.symm U W ∧
      (U⊆actualOriginalPrimaryNativeOpen Data r.val.1.1 i ∩
        actualOriginalPrimaryNativeOpen Data r.val.1.2 i) ∧
      (∀z∈U, (Data.atlas.chart i.1).symm z.2∈Data.atlas.inner i.1) ∧
      (∀z∈K, ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2)∈
        incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2) := by
  intro q K
  let pair := actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W
  let pull : Ep × M → P × M := fun z => ((Data.parameterChart i.2).symm z.1,z.2)
  have hPull : ContinuousOn pull W :=
    ((Data.parameterChart i.2).symm.continuousOn.comp continuous_fst.continuousOn hParam).prodMk
      continuous_snd.continuousOn
  let Wp := W ∩ pull ⁻¹' incrementsOriginalParameterRegion Data
  have hWp : IsOpen Wp :=
    hPull.isOpen_inter_preimage hW (hd.parameter_open.prod isOpen_univ)
  have hPullSupport (nu : Fin Data.primaryCount) (y : Ep × M)
      (hyTheta : y∈tsupport theta)
      (hy : y∈incrementsGlobalRelativeSupport W (fun z=>Data.cutoff nu (pull z))) :
      pull y∈incrementsOriginalRelativeCutoffSupport Data nu := by
    have hyWp : y∈incrementsGlobalRelativeSupport Wp (fun z=>Data.cutoff nu (pull z)) := by
      rw [parameterRound2_global_relativeSupport_eq Wp hWp]
      have hyOld := (parameterRound2_global_relativeSupport_eq W hW
        (fun z=>Data.cutoff nu (pull z))) ▸ hy
      exact ⟨⟨hyOld.1,hOriginal y hyTheta⟩,hyOld.2⟩
    exact actual_relative_support_pullback_subset Wp (incrementsOriginalParameterRegion Data)
      pull (hPull.mono inter_subset_left) (fun z hz=>hz.2) (Data.cutoff nu) hyWp
  have hPairPull (y : Ep × M) (hyTheta : y∈tsupport theta) (hy : y∈pair) : pull y∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 :=
    ⟨hPullSupport r.val.1.1 y hyTheta hy.1,hPullSupport r.val.1.2 y hyTheta hy.2⟩
  let carrier := tsupport theta ∩ pair
  have hCarrier : IsCompact carrier := actual_compact_interaction_carrier
    (tsupport theta) W hCompact (fun y hy => (hThetaSupport hy).1)
    (fun z => Data.cutoff r.val.1.1 (pull z)) (fun z => Data.cutoff r.val.1.2 (pull z))
  have hCarrierSource : carrier⊆q.source := fun y hy => (hThetaSupport hy.1).2
  have hK : IsCompact K := hCarrier.image_of_continuousOn (q.continuousOn.mono hCarrierSource)
  let W0 := W ∩ Prod.snd ⁻¹' Data.atlas.inner i.1
  have hW0 : IsOpen W0 := hW.inter ((Data.atlas.inner_open i.1).preimage continuous_snd)
  let U := (q.target ∩ q.symm ⁻¹' W0) ∩
    (actualOriginalPrimaryNativeOpen Data r.val.1.1 i ∩ actualOriginalPrimaryNativeOpen Data r.val.1.2 i)
  have hU : IsOpen U :=
    (q.symm.continuousOn.isOpen_inter_preimage q.open_target hW0).inter
      ((actualOriginalPrimaryNativeOpen_isOpen Data hd r.val.1.1 i).inter
        (actualOriginalPrimaryNativeOpen_isOpen Data hd r.val.1.2 i))
  have hKpair : ∀z∈K, ((Data.parameterChart i.2).symm z.1,(Data.atlas.chart i.1).symm z.2)∈
      incrementsOriginalRelativeCutoffSupport Data r.val.1.1 ∩
        incrementsOriginalRelativeCutoffSupport Data r.val.1.2 := by
    rintro _ ⟨y,hy,rfl⟩
    have hh := hPairPull y hy.1 hy.2
    change ((Data.parameterChart i.2).symm y.1,(Data.atlas.chart i.1).symm ((Data.atlas.chart i.1) y.2))∈_
    rwa [(Data.atlas.chart i.1).left_inv (hCarrierSource hy).2]
  have hKU : K⊆U := by
    rintro _ ⟨y,hy,rfl⟩
    have hyW := (hThetaSupport hy.1).1
    have hyq := hCarrierSource hy
    have hpull := hKpair _ ⟨y,hy,rfl⟩
    have hprim (nu : Fin Data.primaryCount) (hsup :
        ((Data.parameterChart i.2).symm (q y).1,(Data.atlas.chart i.1).symm (q y).2)∈
          incrementsOriginalRelativeCutoffSupport Data nu) : q y∈actualOriginalPrimaryNativeOpen Data nu i :=
      round3_prepared_native_primary_mem Data i nu (q y) (q.map_source hyq).2 (hParam y hyW)
        ⟨hd.cutoff_support_local nu hsup,incrementsOriginalRelativeCutoffSupport_subset Data nu hsup⟩
    refine ⟨⟨q.map_source hyq,?_⟩,hprim r.val.1.1 hpull.1,hprim r.val.1.2 hpull.2⟩
    change q.symm (q y)∈W0
    rw [q.left_inv hyq]
    exact ⟨hyW,hInner y hy.1⟩
  exact ⟨hK,U,hU,hKU,fun z hz=>hz.1.1,fun z hz=>hz.1.2.1,
    fun z hz=>hz.2,fun z hz=>hz.1.2.2,hKpair⟩

/-- Actual primitive geometry, before any order, scale, adapted chart or
solver is selected. The numerical witnesses depend on the fixed original
map and chosen phase family, exactly as compact Good permits. -/
theorem original_native_primitive_signed_region_exists
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (W : Set (Ep × M)) (hW : IsOpen W)
    (hParam : ∀w∈W, w.1∈(Data.parameterChart i.2).target)
    (theta : Ep × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hOriginal : ∀y∈tsupport theta,
      ((Data.parameterChart i.2).symm y.1,y.2)∈incrementsOriginalParameterRegion Data)
    (hThetaSupport : tsupport theta ⊆ W ∩
      (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source)
    (hInner : ∀y∈tsupport theta, y.2∈Data.atlas.inner i.1) :
    ∃ (mu Mb R buffer coordinateBound kernel lower nativeTwo : ℝ) (Phase : ℕ → ℝ),
      0<mu ∧ 0<Mb ∧ 0<R ∧ 0<buffer ∧ 0<coordinateBound ∧ 0<kernel ∧ 0<lower ∧ 0≤nativeTwo ∧
      (∀j, 0≤Phase j) ∧ Phase 1≤Mb ∧ buffer*Phase 2≤Mb ∧
      Nonempty (NativePrimitiveSignedRegion Data i r W theta
        mu R buffer coordinateBound kernel lower nativeTwo Phase) := by
  let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
  let K := q '' (tsupport theta ∩ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 W)
  obtain ⟨hK,U,hU,hKU,hTarget,hParent,hActive,hInnerU,hKpair⟩ :=
    original_signed_carrier_neighborhood Data hd i r W hW hParam theta hCompact hOriginal hThetaSupport hInner
  obtain ⟨kernel,lower,U0,hKernel,hLower,hU0,hKU0,hU0U,hFirst,hRestriction⟩ :=
    original_signed_compact_reserves Data hd hs hp hImm i r K U hK hU hKU hActive hKpair
  let phase := fun z : X => actualOriginalParameterSignedPhase Data i r.val (z.1,(Data.atlas.chart i.1).symm z.2)
  have hActive0 : U0⊆actualOriginalPrimaryNativeOpen Data r.val.1.1 i ∩
      actualOriginalPrimaryNativeOpen Data r.val.1.2 i := hU0U.trans hActive
  have hNative0 : U0⊆actualOriginalNativeOpen Data i := fun z hz=>
    round3_prepared_primary_native_subset Data i r.val.1.1 (hActive0 hz).1
  have hPhase : ContDiffOn ℝ ∞ phase U0 :=
    (round3_actual_original_signed_native_phase_smooth Data hd hs i r.val).mono hActive0
  have hMap : ContDiffOn ℝ ∞ (actualOriginalNativeMap Data i) U0 :=
    (actualOriginalNativeMap_contDiffOn_parameter_open Data hd hs i).mono hNative0
  have hNoncritical : ∀z∈K, (fderiv ℝ phase z).comp (ContinuousLinearMap.inr ℝ Ep D)≠0 := by
    intro z hz
    have hGood := actual_original_parameter_signed_secondary_phase_good Data hd hs hp i r
      (z.1,(Data.atlas.chart i.1).symm z.2) (hKpair z hz)
    exact round3_actual_host_phase_spatial_ne_zero (Data.atlas.chart i.1)
      (hd.atlas_smooth.chart_mem i.1) (actualOriginalParameterSignedPhase Data i r.val) z
      (actualOriginalNativeMap_source_target Data i (hNative0 (hKU0 hz)).1)
      ((hPhase.contDiffAt (hU0.mem_nhds (hKU0 hz))).differentiableAt (by simp)) hGood.1
  obtain ⟨mu,Mb,R,buffer,coordinateBound,nativeTwo,O,Phase,hMu,hMb,hR,hBuffer,hCoordinate,hTwo,
    hO,hKO,hOU,hRadius,hBufferO,hCoordinates,hPhaseNN,hPhaseOne,hPhaseTwo,hPhaseO,hMuK,hPhaseJets,hMapJets⟩ :=
    compact_phase_native_two_jet_budgets phase (actualOriginalNativeMap Data i) K U0 hK hU0 hKU0 hPhase hMap hNoncritical
  refine ⟨mu,Mb,R,buffer,coordinateBound,kernel,lower,nativeTwo,Phase,
    hMu,hMb,hR,hBuffer,hCoordinate,hKernel,hLower,hTwo,hPhaseNN,hPhaseOne,hPhaseTwo,?_⟩
  exact ⟨{
    domain := O
    center := 0
    isOpen := hO
    carrier_radius := hRadius
    carrier_buffer := hBufferO
    target := hOU.trans (hU0U.trans hTarget)
    parent := fun z hz=>hParent (hU0U (hOU hz))
    active := hOU.trans hActive0
    inner := fun z hz=>hInnerU z (hU0U (hOU hz))
    native_first := fun z hz=>hFirst z (hOU hz)
    native_jets := hMapJets
    coordinates := hCoordinates
    phase_smooth := hPhaseO
    phase_noncritical := hMuK
    phase_jets := hPhaseJets
    original_kernel := fun z hz=>hRestriction z (hOU hz) }⟩

end GlobalEmbedding.Continuation.OriginalIncrements
#print axioms GlobalEmbedding.Continuation.OriginalIncrements.original_native_primitive_signed_region_exists
