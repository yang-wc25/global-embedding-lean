import Repair.FullIncrementNovOpenSourceModel
import Repair.FullIncrementNovOpenSecondaryPieces
import Probes.Round3PreparedParameterSecondaryStablePiece
import Probes.Round3PreparedParameterSecondaryLift

/-! The same signed-secondary reference piece is an actual piece for the
internal source-slice model. Its source and target lie over parameterOpen;
no whole-parameter equality or joint extension is assumed. The canonical
cross-observer host/slice packet and transverse margin are then produced on
the unchanged original Data, with the same literal physical choice.
-/

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
local notation "Tdata" => EuclideanSpace ℝ {p : Fin m × Fin m // Prod.fst p ≤ Prod.snd p}
local notation "𝓙" => 𝓘(ℝ,D)

theorem fullIncrementNov_secondary_target_parameter_open
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W)
    (z : X) (hz : z ∈ piece.native.target) :
    (Data.parameterChart i.2).symm z.1 ∈ Data.parameterOpen := by
  have hSource := piece.native_source (piece.native.map_target hz)
  have hOpen := actualOriginalNativeOpen_parameter Data i hSource
  have hP := (round3_prepared_signed_native_preserves_phase Data hd hs i r W piece).1
    (piece.native.symm z) (piece.native.map_target hz)
  rw [piece.native.right_inv hz] at hP
  simpa only [← hP] using hOpen

def fullIncrementNovSecondarySelfStable
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W) :
    Round3PreparedParameterStableSecondaryPiece Data hd hs i r W piece
      (fullIncrementNovOriginalSourceSlice Data) (fullIncrementNov_original_source_slice_smooth Data hd hs) where
  piece := piece
  cutoff := rfl
  carrier := rfl
  forward := rfl
  inverse := rfl
  slices := fun _ => rfl
  source_subset := Subset.rfl
  target_subset := Subset.rfl
  cF_eq := rfl
  cT_eq := rfl
  MH_eq := rfl
  Bnative_eq := rfl
  Tinv_eq := rfl
  Forward_eq := rfl
  first := by
    intro z hz v
    have hh := piece.first z hz v
    change (piece.cF/16)*‖v‖^2 ≤ ‖fderiv ℝ
      (actualOriginalOpenParameterSlice Data i z.1 ∘ (piece.slices z.1).symm) z.2 v‖^2
    exact (mul_le_mul_of_nonneg_right (by linarith [piece.cF_pos] : piece.cF/16 ≤ piece.cF)
      (sq_nonneg ‖v‖)).trans hh
  transverse := by
    intro z hz v
    have hh := piece.transverse z hz v
    exact (mul_le_mul_of_nonneg_right (by linarith [piece.cT_pos] : piece.cT/16 ≤ piece.cT)
      (sq_nonneg ‖v‖)).trans hh
  immersion := by
    intro z hz
    have hp := fullIncrementNov_secondary_target_parameter_open Data hd hs i r W piece z hz
    rw [fullIncrementNov_original_source_slice_eq Data _ hp]
    exact hImm.immersion _ hp _

theorem fullIncrementNov_original_secondary_cross_host
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W)
    (observer : Fin Data.parameterCount) :
    let choice := round3PreparedParameterSecondaryChoice Data hd hs i r W piece
    let native := (choice.pullback (Data.parameterChart observer)).toNative
    let b := round3ParameterCrossNativeChart (Data.parameterChart i.2) (Data.parameterChart observer) piece.native
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData (Data.atlas.chart i.1) b
        (actualOriginalParameterSignedPhase Data (i.1,observer) r.val) e ∧
      b.source ⊆ actualOriginalNativeOpen Data (i.1,observer) ∧
      (∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source,
        w.2 ∈ Data.atlas.inner i.1) ∧
      native = ⟨Data.atlas.chart i.1,actualHostAdaptedChart (Data.atlas.chart i.1) b,
        (fun p x => (e p).symm x),fun z => choice.cutoff ((Data.parameterChart observer).symm z.1,z.2)⟩ ∧
      ∀ z ∈ b.target, ∀ v : Tdata, piece.cT*‖v‖^2 ≤
        ‖incrementsModeAmbientTransverseFrame
          (actualOriginalOpenParameterSlice Data (i.1,observer) z.1)
          (actualOriginalOpenParameterSlice_contMDiff Data hd hs (i.1,observer) z.1)
          (e z.1).symm z.2 v‖^2 := by
  intro choice native b
  let Bp := Data.parameterChart i.2
  let Bo := Data.parameterChart observer
  let C := Bp.symm.trans Bo
  obtain ⟨e,hData,hNative,hActive,hSlices⟩ :=
    round3_prepared_signed_cross_native_data Data hd hs i observer r W piece
  have hSame (p : Ep) : ((e p).symm : D → M) = (piece.slices (Bp (Bo.symm p))).symm :=
    funext (hSlices p)
  have hCrossInner (w : Ep × M)
      (hw : w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) b).source) :
      w.2 ∈ Data.atlas.inner i.1 := by
    have hEq := round3Parameter_cross_host_conjugation Bp Bo (Data.atlas.chart i.1) piece.native
      (round3_prepared_signed_native_preserves_phase Data hd hs i r W piece).1
    have hh : w ∈ (round3ParameterChartPullback Bo (round3ParameterChartPullback Bp.symm
        (actualHostAdaptedChart (Data.atlas.chart i.1) piece.native))).source := by rwa [← hEq]
    have ho := (round3ParameterChartPullback_source Bo (round3ParameterChartPullback Bp.symm
      (actualHostAdaptedChart (Data.atlas.chart i.1) piece.native)) w).mp hh
    have hpi := (round3ParameterChartPullback_source Bp.symm
      (actualHostAdaptedChart (Data.atlas.chart i.1) piece.native) (Bo.symm w.1,w.2)).mp ho.2.1
    exact piece.source_inner (Bp (Bo.symm w.1),w.2) hpi.2.1
  have hChart : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1) b :=
    (round3Parameter_cross_host_conjugation Bp Bo (Data.atlas.chart i.1) piece.native
      (round3_prepared_signed_native_preserves_phase Data hd hs i r W piece).1).symm
  have hC : native.c = fun p x => (e p).symm x := by
    funext p x
    exact (hSlices p x).symm
  refine ⟨e,hData,hNative,hCrossInner,?_,?_⟩
  · change ActualOriginalSecondaryChoice.mk native.host native.chart native.c native.cutoff = _
    rw [hChart,hC]
    rfl
  · intro z hz v
    have ht := (round3ParameterChartPullback_target C piece.native z).mp hz
    have hh := piece.transverse (Bp (Bo.symm z.1),z.2) ht.2.1 v
    have hFsame : actualOriginalOpenParameterSlice Data i (Bp (Bo.symm z.1)) =
        actualOriginalOpenParameterSlice Data (i.1,observer) z.1 := by
      funext x
      change (if Bp.symm (Bp (Bo.symm z.1)) ∈ Data.parameterOpen then
        Data.F (Bp.symm (Bp (Bo.symm z.1)),x) else 0) = _
      rw [Bp.left_inv ht.1.2]
      rfl
    simpa only [hFsame,hSame] using hh

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNovSecondarySelfStable
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_secondary_cross_host
