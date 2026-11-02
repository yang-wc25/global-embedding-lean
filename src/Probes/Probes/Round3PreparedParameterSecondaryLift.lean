import Probes.Round3PreparedParameterSecondaryCrossData
import Probes.Round3ParameterNativeParent

/-! One physical signed-secondary choice is constructed from a fixed actual
reference piece. Every observer receives its canonical two-sided conjugate;
the real host/slice packet is supplied for that same native choice. -/
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
local notation "𝓙" => 𝓘(ℝ,D)

 def round3PreparedParameterSecondaryChoice
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W) :
    Round3ParameterSecondaryChoice P M m where
  host := Data.atlas.chart i.1
  chart := round3ParameterChartPullback (Data.parameterChart i.2).symm
    (actualHostAdaptedChart (Data.atlas.chart i.1) piece.native)
  c := fun p x => (piece.slices ((Data.parameterChart i.2) p)).symm x
  cutoff := round3ParameterSupportedPullback
    (round3ParameterProductChart (Data.parameterChart i.2)) piece.cutoff

 theorem round3_prepared_parameter_secondary_preserves
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W) :
    Round3ParameterChartPreserves
      (round3PreparedParameterSecondaryChoice Data hd hs i r W piece).chart := by
  apply round3ParameterChartPullback_preserves
  intro z hz
  exact (piece.data.2.2.2.1 z hz).1

 theorem round3_prepared_parameter_secondary_native_presentation
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount) (observer : Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W) :
    let choice := round3PreparedParameterSecondaryChoice Data hd hs i r W piece
    let native := (choice.pullback (Data.parameterChart observer)).toNative
    let bC := round3ParameterCrossNativeChart (Data.parameterChart i.2)
      (Data.parameterChart observer) piece.native
    ∃ e : Ep → OpenPartialHomeomorph M D,
      ActualOriginalHostSliceData (Data.atlas.chart i.1) bC
        (actualOriginalParameterSignedPhase Data (i.1,observer) r.val) e ∧
      bC.source ⊆ actualOriginalNativeOpen Data (i.1,observer) ∧
      (∀ w ∈ (actualHostAdaptedChart (Data.atlas.chart i.1) bC).source,
        ((Data.parameterChart observer).symm w.1,w.2) ∈
          Data.primaryDomain r.val.1.1 ∩ incrementsOriginalParameterRegion Data ∧
        ((Data.parameterChart observer).symm w.1,w.2) ∈
          Data.primaryDomain r.val.1.2 ∩ incrementsOriginalParameterRegion Data) ∧
      native = ⟨Data.atlas.chart i.1,actualHostAdaptedChart (Data.atlas.chart i.1) bC,
        (fun p x => (e p).symm x),
        (fun z => choice.cutoff ((Data.parameterChart observer).symm z.1,z.2))⟩ := by
  intro choice native bC
  obtain ⟨e,he,hn,ha,hi⟩ :=
    round3_prepared_signed_cross_native_data Data hd hs i observer r W piece
  refine ⟨e,he,hn,ha,?_⟩
  have hc : native.chart = actualHostAdaptedChart (Data.atlas.chart i.1) bC :=
    (round3Parameter_cross_host_conjugation (Data.parameterChart i.2)
      (Data.parameterChart observer) (Data.atlas.chart i.1) piece.native
      (round3_prepared_signed_native_preserves_phase Data hd hs i r W piece).1).symm
  have hi' : native.c = fun p x => (e p).symm x := by
    funext p x
    exact (hi p x).symm
  change ActualOriginalSecondaryChoice.mk native.host native.chart native.c native.cutoff = _
  rw [hc,hi']
  rfl

 theorem round3_prepared_parameter_secondary_cutoff_geometry
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (W : Set (Ep × M))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r W)
    (theta : P × M → ℝ) (hCompact : IsCompact (tsupport theta))
    (hSupport : tsupport theta ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hNative : tsupport (round3ParameterNativeParent (Data.parameterChart i.2) theta) ⊆
      (round3ParameterProductChart (M := M) (Data.parameterChart i.2)) '' tsupport theta)
    (hParent : tsupport piece.cutoff ⊆
      tsupport (round3ParameterNativeParent (Data.parameterChart i.2) theta)) :
    let choice := round3PreparedParameterSecondaryChoice Data hd hs i r W piece
    ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ choice.cutoff ∧
    IsCompact (tsupport choice.cutoff) ∧ tsupport choice.cutoff ⊆ tsupport theta := by
  intro choice
  let q := round3ParameterProductChart (M := M) (Data.parameterChart i.2)
  have hCarrier : ∀ z ∈ q.source, q z ∈ tsupport piece.cutoff → z ∈ tsupport theta := by
    intro z hz he
    exact round3Parameter_native_parent_source (Data.parameterChart i.2) theta
      hSupport hNative z hz.1 (hParent he)
  have hSub := round3ParameterSupportedPullback_support q piece.cutoff
    (tsupport theta) (isClosed_tsupport _) hCarrier
  exact ⟨round3ParameterSupportedPullback_smooth q piece.cutoff (tsupport theta)
      (isClosed_tsupport _) hSupport hCarrier
      (round3ParameterProductChart_smooth (Data.parameterChart i.2) (hd.parameter_charts_smooth i.2))
      piece.cutoff_smooth.contMDiffOn,
    hCompact.of_isClosed_subset (isClosed_tsupport _) hSub,hSub⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_native_presentation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_cutoff_geometry
