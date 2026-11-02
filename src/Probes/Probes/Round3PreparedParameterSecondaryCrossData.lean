import Probes.Round3ParameterCrossNativeData
import Probes.Round3PreparedSignedReferencePiece
import Probes.Round3ParameterSecondaryPullback

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

theorem round3_prepared_signed_native_preserves_phase
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W) :
    Round3ParameterChartPreserves piece.native ∧
    ∀ z ∈ piece.native.source, (piece.native z).2 0 =
      actualOriginalParameterSignedPhase Data i r.val (z.1,(Data.atlas.chart i.1).symm z.2) := by
  have hg := actual_host_slice_geometry_inputs (Data.atlas.chart i.1)
    (hd.atlas_smooth.chart_mem i.1) piece.native _ piece.slices piece.data
  have hf (z : X) (hz : z ∈ piece.native.source) :
      (piece.native z).1 = z.1 ∧ (piece.native z).2 0 =
        actualOriginalParameterSignedPhase Data i r.val (z.1,(Data.atlas.chart i.1).symm z.2) := by
    let q := actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)
    have hqz : z ∈ q.target := hg.1 hz
    have hsrc : q.symm z ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) piece.native).source :=
      ⟨q.map_target hqz,by change q (q.symm z) ∈ piece.native.source; rwa [q.right_inv hqz]⟩
    have hh := piece.data.2.2.2.1 (q.symm z) hsrc
    change (piece.native (q (q.symm z))).1 = z.1 ∧
      (piece.native (q (q.symm z))).2 0 = _ at hh
    rw [q.right_inv hqz] at hh
    exact hh
  exact ⟨fun z hz => (hf z hz).1,fun z hz => (hf z hz).2⟩

theorem round3_prepared_signed_cross_native_data
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data)
    (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (observer : Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W) :
    let bC := round3ParameterCrossNativeChart (Data.parameterChart i.2) (Data.parameterChart observer) piece.native
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData (Data.atlas.chart i.1) bC
        (actualOriginalParameterSignedPhase Data (i.1,observer) r.val) e ∧
      bC.source ⊆ actualOriginalNativeOpen Data (i.1,observer) ∧
      (∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) bC).source,
        ((Data.parameterChart observer).symm w.1,w.2) ∈
          Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
        ((Data.parameterChart observer).symm w.1,w.2) ∈ Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data) ∧
      ∀ p x, (e p).symm x =
        ((piece.slices ((Data.parameterChart i.2) ((Data.parameterChart observer).symm p))).symm x) := by
  intro bC
  let Bp := Data.parameterChart i.2
  let Bo := Data.parameterChart observer
  let C := Bp.symm.trans Bo
  let c := Data.atlas.chart i.1
  have hOld := actual_host_slice_geometry_inputs c (hd.atlas_smooth.chart_mem i.1)
    piece.native _ piece.slices piece.data
  have hNP := round3_prepared_signed_native_preserves_phase Data hd hs i r W piece
  have hSmooth := round3Parameter_cross_native_smooth (m := m) Bp Bo
    (hd.parameter_charts_smooth i.2) (hd.parameter_charts_smooth observer)
    piece.native hOld.2.1 hOld.2.2.1
  have hSource : bC.source ⊆ (actualOriginalHostJointChart («Ep» := Ep) c).target := by
    intro z hz
    have hh := (round3ParameterChartPullback_source C piece.native z).mp hz
    exact ⟨mem_univ _,(hOld.1 hh.2.1).2⟩
  have hPhase : ∀ z ∈ bC.source, (bC z).2 0 = actualOriginalParameterSignedPhase Data (i.1,observer) r.val (z.1,c.symm z.2) := by
    intro z hz
    have hh := (round3ParameterChartPullback_source C piece.native z).mp hz
    change (piece.native (C.symm z.1,z.2)).2 0 = _
    rw [hNP.2 _ hh.2.1]
    have hleft : (Data.parameterChart i.2).symm (C.symm z.1) =
        (Data.parameterChart observer).symm z.1 := Bp.left_inv hh.1.2
    simp only [actualOriginalParameterSignedPhase, hleft]
    rfl
  have hParam : Round3ParameterChartPreserves bC := round3ParameterChartPullback_preserves C piece.native hNP.1
  obtain ⟨hat,ha,hai,hforw,e,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩ :=
    actual_adapted_chart_original_host c (hd.atlas_smooth.chart_mem i.1)
      (actualOriginalParameterSignedPhase Data (i.1,observer) r.val) bC hSource hSmooth.1 hSmooth.2 hParam hPhase
  have hNative : bC.source ⊆ actualOriginalNativeOpen Data (i.1,observer) := by
    intro z hz
    have hh := (round3ParameterChartPullback_source C piece.native z).mp hz
    have hOldNative := piece.native_source hh.2.1
    have hOpen := actualOriginalNativeOpen_parameter Data i hOldNative
    change Bp.symm (Bp (Bo.symm z.1)) ∈ Data.parameterOpen at hOpen
    rw [Bp.left_inv hh.1.2] at hOpen
    exact (round3Parameter_originalNativeOpen_iff Data (i.1,observer) z).mpr
      ⟨(hSource hz).2,hh.1.1,hOpen⟩
  have hActive : ∀ w ∈ (actualHostAdaptedChart c bC).source,
      (Bo.symm w.1,w.2) ∈ Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
        ((Data.parameterChart observer).symm w.1,w.2) ∈ Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data := by
    intro w hw
    have hEq := round3Parameter_cross_host_conjugation Bp Bo c piece.native hNP.1
    have hh : w ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm
        (actualHostAdaptedChart c piece.native))).source := by rwa [← hEq]
    have ho := (round3ParameterChartPullback_source Bo (round3ParameterChartPullback Bp.symm
      (actualHostAdaptedChart c piece.native)) w).mp hh
    have hpi := (round3ParameterChartPullback_source Bp.symm
      (actualHostAdaptedChart c piece.native) (Bo.symm w.1,w.2)).mp ho.2.1
    have hp := piece.active (Bp (Bo.symm w.1),w.2) hpi.2.1
    have hleft : (Data.parameterChart i.2).symm (Bp (Bo.symm w.1)) =
        (Data.parameterChart observer).symm w.1 := Bp.left_inv hpi.1
    simpa only [hleft] using hp
  refine ⟨e,⟨hat,ha,hai,hforw,he,hes,het,hef,hei,hpair,hphase,hback,hforward,hbj,hfj⟩,
    hNative,hActive,?_⟩
  intro p x
  rw [hei]
  rcases piece.data with ⟨hat0,ha0,hai0,hforw0,he0,hes0,het0,hef0,hei0,hpair0,hphase0,hback0,hforward0,hbj0,hfj0⟩
  exact (hei0 (Bp (Bo.symm p)) x).symm

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_signed_cross_native_data
