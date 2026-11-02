import Probes.Round3ParameterCrossNativeRegularity

/-! Every canonical cross-B primary chart is supplied as an actual original
host/slice packet. Its native open domain and physical active domain are
proved, and the supplied slice inverse is the SAME original inverse function.
This is real constructed input for the original raw producer. -/

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
local notation "X" => Ep × D
local notation "𝓙" => 𝓘(ℝ,D)

theorem round3Parameter_originalNativeOpen_iff
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : X) :
    z ∈ actualOriginalNativeOpen Data i ↔
      z.2 ∈ (Data.atlas.chart i.1).target ∧ z.1 ∈ (Data.parameterChart i.2).target ∧
        (Data.parameterChart i.2).symm z.1 ∈ Data.parameterOpen := by
  have hp := congrArg Prod.fst ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  have hx := congrArg Prod.snd ((parameterTensorModelEquiv (m+1) d).symm_apply_apply z)
  change incrementsOriginalParameterPoint (parameterTensorModelEquiv (m+1) d z) = z.1 at hp
  change incrementsOriginalSourcePoint (parameterTensorModelEquiv (m+1) d z) = z.2 at hx
  simp only [actualOriginalNativeOpen,incrementsOriginalDifferentiation,mem_preimage,mem_inter_iff,
    mem_setOf_eq,incrementsOriginalJointPoint,incrementsOriginalParameterRegion,mem_prod,mem_univ,
    hp,hx,and_true,and_assoc]

theorem round3Parameter_actual_cross_native_data
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (ip observer : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) :
    let bC := round3ParameterCrossNativeChart (Data.parameterChart ip) (Data.parameterChart observer) piece.native
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData (Data.atlas.chart piece.host) bC
        (fun z : Ep × M => Data.phase nu ((Data.parameterChart observer).symm z.1,z.2)) e ∧
      bC.source ⊆ actualOriginalNativeOpen Data (piece.host,observer) ∧
      (∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart piece.host) bC).source,
        ((Data.parameterChart observer).symm w.1,w.2) ∈
          Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data) ∧
      ∀ p x, (e p).symm x =
        ((piece.slices ((Data.parameterChart ip) ((Data.parameterChart observer).symm p))).symm x) := by
  intro bC
  let Bp := Data.parameterChart ip
  let Bo := Data.parameterChart observer
  let C := Bp.symm.trans Bo
  let c := Data.atlas.chart piece.host
  have hOld := actual_host_slice_geometry_inputs c (hd.atlas_smooth.chart_mem piece.host)
    piece.native _ piece.slices piece.data
  have hNP := round3Parameter_primary_native_preserves_phase Data hd ip nu W piece
  have hSmooth := round3Parameter_cross_native_smooth (m := m) Bp Bo
    (hd.parameter_charts_smooth ip) (hd.parameter_charts_smooth observer)
    piece.native hOld.2.1 hOld.2.2.1
  have hSource : bC.source ⊆ (actualOriginalHostJointChart («Ep» := Ep) c).target := by
    intro z hz
    have hh := (round3ParameterChartPullback_source C piece.native z).mp hz
    exact ⟨mem_univ _,(hOld.1 hh.2.1).2⟩
  have hPhase : ∀ z ∈ bC.source, (bC z).2 0 = Data.phase nu (Bo.symm z.1,c.symm z.2) := by
    intro z hz
    have hh := (round3ParameterChartPullback_source C piece.native z).mp hz
    change (piece.native (C.symm z.1,z.2)).2 0 = _
    rw [hNP.2 _ hh.2.1]
    change Data.phase nu (Bp.symm (Bp (Bo.symm z.1)),c.symm z.2) = _
    rw [Bp.left_inv hh.1.2]
  have hParam : Round3ParameterChartPreserves bC := round3ParameterChartPullback_preserves C piece.native hNP.1
  obtain ⟨hat,ha,hai,hforw,e,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩ :=
    actual_adapted_chart_original_host c (hd.atlas_smooth.chart_mem piece.host)
      (fun z : Ep × M => Data.phase nu (Bo.symm z.1,z.2)) bC hSource hSmooth.1 hSmooth.2 hParam hPhase
  have hNative : bC.source ⊆ actualOriginalNativeOpen Data (piece.host,observer) := by
    intro z hz
    have hh := (round3ParameterChartPullback_source C piece.native z).mp hz
    have hOldNative := piece.native_source hh.2.1
    have hOpen := actualOriginalNativeOpen_parameter Data (piece.host,ip) hOldNative
    change Bp.symm (Bp (Bo.symm z.1)) ∈ Data.parameterOpen at hOpen
    rw [Bp.left_inv hh.1.2] at hOpen
    exact (round3Parameter_originalNativeOpen_iff Data (piece.host,observer) z).mpr
      ⟨(hSource hz).2,hh.1.1,hOpen⟩
  have hActive : ∀ w ∈ (actualHostAdaptedChart c bC).source,
      (Bo.symm w.1,w.2) ∈ Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data := by
    intro w hw
    have hEq := round3Parameter_cross_host_conjugation Bp Bo c piece.native hNP.1
    have hh : w ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm
        (actualHostAdaptedChart c piece.native))).source := by rwa [← hEq]
    have ho := (round3ParameterChartPullback_source Bo (round3ParameterChartPullback Bp.symm
      (actualHostAdaptedChart c piece.native)) w).mp hh
    have hpi := (round3ParameterChartPullback_source Bp.symm
      (actualHostAdaptedChart c piece.native) (Bo.symm w.1,w.2)).mp ho.2.1
    have hp := piece.active (Bp (Bo.symm w.1),w.2) hpi.2.1
    change (Bp.symm (Bp (Bo.symm w.1)),w.2) ∈
      Data.primaryDomain nu ∩ incrementsOriginalParameterRegion Data at hp
    rwa [Bp.left_inv hpi.1] at hp
  refine ⟨e,⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩,
    hNative,hActive,?_⟩
  intro p x
  rw [hei]
  rcases piece.data with ⟨hat0,ha0,hai0,hforw0,he0,hes0,het0,hef0,hei0,hpair0,hphase0,hback0,hforward0,hbj0,hfj0⟩
  exact (hei0 (Bp (Bo.symm p)) x).symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_actual_cross_native_data
