import Repair.FullIncrementNovOpenPrimaryPieces
import Probes.Round3PreparedParameterSecondaryPieces

/-! Actual signed and doubled secondary pieces on the original parameter
open set. The finite packet is selected before scales, solver lengths and
observation orders. Only its analysis-domain annotation is enlarged; its
native charts, source slices, cutoffs, interaction carriers, phases and
positive transverse reserves remain the actual constructed ones.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation
variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

def fullIncrementNovSecondaryPieceEnlarge
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (W U : Set (Ep × M)) (hW : IsOpen W) (hU : IsOpen U) (hWU : W ⊆ U)
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W)
    (hCutW : tsupport piece.cutoff ⊆ W) :
    Round3PreparedSignedReferencePiece Data hd hs i r U := {
  piece with
  source_domain := piece.source_domain.trans hWU
  carrier_eq := by
    rw [piece.carrier_eq]
    ext z
    simp only [actualOriginalParameterSupportPair,
      parameterRound2_global_relativeSupport_eq W hW,
      parameterRound2_global_relativeSupport_eq U hU,mem_inter_iff]
    constructor
    · rintro ⟨hc,⟨hw,hn⟩,⟨_,hm⟩⟩
      exact ⟨hc,⟨hWU hw,hn⟩,⟨hWU hw,hm⟩⟩
    · rintro ⟨hc,⟨_,hn⟩,⟨_,hm⟩⟩
      exact ⟨hc,⟨hCutW hc,hn⟩,⟨hCutW hc,hm⟩⟩ }

variable [T2Space M]

theorem fullIncrementNov_original_open_secondary_pieces
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    Nonempty (Round3PreparedParameterSecondaryPacket Data hd hs theta) := by
  let W := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    ((Data.parameterChart i.2).target ∩ (Data.parameterChart i.2).symm ⁻¹' Data.parameterOpen) ×ˢ
      (univ : Set M)
  let U := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  have hW (i : Fin Data.atlas.count × Fin Data.parameterCount) : IsOpen (W i) :=
    ((Data.parameterChart i.2).symm.continuousOn.isOpen_inter_preimage
      (Data.parameterChart i.2).open_target hd.parameter_open).prod isOpen_univ
  have hU (i : Fin Data.atlas.count × Fin Data.parameterCount) : IsOpen (U i) :=
    (Data.parameterChart i.2).open_target.prod isOpen_univ
  have hWU (i : Fin Data.atlas.count × Fin Data.parameterCount) : W i ⊆ U i :=
    fun _ hz => ⟨hz.1.1,hz.2⟩
  have hSupport' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz => ⟨(hSupport i hz).1.1,mem_univ _⟩
  have hLocal (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : P × M)
      (hz : z ∈ tsupport (theta i)) : ((Data.parameterChart i.2) z.1,z.2) ∈ W i := by
    have ht := hSupport i hz
    refine ⟨⟨(Data.parameterChart i.2).map_source ht.1.1,?_⟩,mem_univ _⟩
    change (Data.parameterChart i.2).symm ((Data.parameterChart i.2) z.1) ∈ Data.parameterOpen
    rw [(Data.parameterChart i.2).left_inv ht.1.1]
    exact ht.1.2
  have hNative (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3Parameter_native_compact_parent (Data.parameterChart i.2)
      (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) (hSupport' i)
  have hNSupport (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆
        W i ∩ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    exact ⟨hLocal i z hz,mem_univ _,Data.atlas.inner_subset i.1 (hSupport i hz).2⟩
  have hInner (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Ep × M)
      (hy : y ∈ tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))) :
      y.2 ∈ Data.atlas.inner i.1 := by
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    exact (hSupport i hz).2
  have hLocalPieces (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
      (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3_actual_original_signed_reference_refinement Data hd hs hp hImm i r (W i) (hW i)
      (fun _ hy => hy.1.1) (fun z hz => ⟨hz.1.2,mem_univ _⟩)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i) (hInner i)
  choose s piece hPart hParent hCount using hLocalPieces
  let out := fun r i (a : s r i) => fullIncrementNovSecondaryPieceEnlarge Data hd hs i r
    (W i) (U i) (hW i) (hU i) (hWU i) (piece r i a)
      ((hParent r i a).trans (fun _ hz => (hNSupport i hz).1))
  have hPartU (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
      (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Ep × M)
      (hy : y ∈ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 (U i)) :
      ∑ a : s r i, (out r i a).cutoff y = round3ParameterNativeParent (Data.parameterChart i.2) (theta i) y := by
    by_cases ht : y ∈ tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
    · have hwy := (hNSupport i ht).1
      have hpW : y ∈ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2 (W i) := by
        simp only [actualOriginalParameterSupportPair,
          parameterRound2_global_relativeSupport_eq (U i) (hU i),mem_inter_iff] at hy
        simp only [actualOriginalParameterSupportPair,
          parameterRound2_global_relativeSupport_eq (W i) (hW i),mem_inter_iff]
        exact ⟨⟨hwy,hy.1.2⟩,⟨hwy,hy.2.2⟩⟩
      exact hPart r i y hpW
    · rw [image_eq_zero_of_notMem_tsupport ht]
      exact Finset.sum_eq_zero (fun a _ =>
        image_eq_zero_of_notMem_tsupport (fun ha => ht (hParent r i a ha)))
  have hLift (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
      (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s r i) :=
    round3_prepared_parameter_secondary_cutoff_geometry Data hd hs i r (U i)
      (out r i a) (theta i) (hCompact i) (hSupport' i) (hNative i).2.2 (hParent r i a)
  exact ⟨{
    s := s
    piece := out
    native_parent := hParent
    smooth := fun r i a => (hLift r i a).1
    compact := fun r i a => (hLift r i a).2.1
    parent := fun r i a => (hLift r i a).2.2
    source := fun r i a => (round3_prepared_parameter_secondary_carrier_source Data hd hs i r
      (out r i a) (theta i) (hSupport' i) (hLift r i a).2.2).1
    partition := fun r i z hz => round3_prepared_parameter_secondary_partition_transport Data hd hs i r
      (out r i) (theta i) (hSupport' i) (fun a => (hLift r i a).2.2) (hPartU r i) z hz
    count := fun r i z => round3_prepared_parameter_secondary_count_transport Data hd hs i r
      (out r i) (theta i) (hSupport' i) (fun a => (hLift r i a).2.2)
      (5^Module.finrank ℝ (Ep × D)) (hCount r i) z }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNovSecondaryPieceEnlarge
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_secondary_pieces
