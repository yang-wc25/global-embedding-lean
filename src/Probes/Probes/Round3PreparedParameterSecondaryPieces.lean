import Probes.Round3PreparedParameterSecondaryTransport
import Probes.Round3PreparedSignedReferenceRefinement
import Probes.Round3PreparedFiniteAssembly

/-! Original signed phases and compact physical parents construct one fixed
all-parameter family of actual signed-secondary choices. All parameter charts
are represented in this family before any observer, scale, or derivative
order is chosen. -/
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

 structure Round3PreparedParameterSecondaryPacket
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ) where
  s : ActualSecondarySignedRecord (Fin Data.primaryCount) →
    (Fin Data.atlas.count × Fin Data.parameterCount) → Finset (Ep × D)
  piece : ∀ r i, s r i → Round3PreparedSignedReferencePiece Data hd hs i r
    ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
  native_parent : ∀ r i a, tsupport (piece r i a).cutoff ⊆
    tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
  smooth : ∀ r i a, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞
    (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece r i a)).cutoff
  compact : ∀ r i a, IsCompact (tsupport
    (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece r i a)).cutoff)
  parent : ∀ r i a, tsupport
    (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece r i a)).cutoff ⊆ tsupport (theta i)
  source : ∀ r i a, round3PreparedParameterSecondaryCarrier Data r
    (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece r i a)) ⊆
    (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece r i a)).chart.source
  partition : ∀ r i z, z ∈ tsupport (Data.cutoff r.val.1.1) ∩ tsupport (Data.cutoff r.val.1.2) →
    ∑ a : s r i, (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece r i a)).cutoff z = theta i z
  count : ∀ r i z, (Finset.univ.filter (fun a : s r i => z ∈
    round3PreparedParameterSecondaryCarrier Data r
      (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece r i a)))).card ≤
        5^Module.finrank ℝ (Ep × D)

variable [T2Space M]
 theorem round3_prepared_actual_parameter_secondary_pieces
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (hImm : IncrementsOriginalSliceImmersionInputs Data) (hAll : Data.parameterSet = univ)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1) :
    Nonempty (Round3PreparedParameterSecondaryPacket Data hd hs theta) := by
  have hOpen (p : P) : p ∈ Data.parameterOpen := hd.parameter_subset (by rw [hAll]; exact mem_univ _)
  let W := fun i : Fin Data.atlas.count × Fin Data.parameterCount => (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  have hW (i : Fin Data.atlas.count × Fin Data.parameterCount) : IsOpen (W i) := (Data.parameterChart i.2).open_target.prod isOpen_univ
  have hSupport' (i : Fin Data.atlas.count × Fin Data.parameterCount) : tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz => ⟨(hSupport i hz).1,mem_univ _⟩
  have hNative (i : Fin Data.atlas.count × Fin Data.parameterCount) := round3Parameter_native_compact_parent (Data.parameterChart i.2)
    (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) (hSupport' i)
  have hNSupport (i : Fin Data.atlas.count × Fin Data.parameterCount) : tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆
      W i ∩ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    have hh := hSupport i hz
    exact ⟨⟨(Data.parameterChart i.2).map_source hh.1,mem_univ _⟩,
      mem_univ _,Data.atlas.inner_subset i.1 hh.2⟩
  have hInner (i : Fin Data.atlas.count × Fin Data.parameterCount) (y : Ep × M)
      (hy : y ∈ tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))) :
      y.2 ∈ Data.atlas.inner i.1 := by
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    exact (hSupport i hz).2
  have hLocal (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3_actual_original_signed_reference_refinement Data hd hs hp hImm i r (W i) (hW i)
      (fun _ hy => hy.1) (fun z _ => ⟨hOpen _,mem_univ _⟩)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i) (hInner i)
  choose s piece hPart hParent hCount using hLocal
  have hLift (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
      (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s r i) :=
    round3_prepared_parameter_secondary_cutoff_geometry Data hd hs i r (W i)
      (piece r i a) (theta i) (hCompact i) (hSupport' i) (hNative i).2.2 (hParent r i a)
  exact ⟨{
    s := s
    piece := piece
    native_parent := hParent
    smooth := fun r i a => (hLift r i a).1
    compact := fun r i a => (hLift r i a).2.1
    parent := fun r i a => (hLift r i a).2.2
    source := fun r i a => (round3_prepared_parameter_secondary_carrier_source Data hd hs i r
      (piece r i a) (theta i) (hSupport' i) (hLift r i a).2.2).1
    partition := fun r i z hz => round3_prepared_parameter_secondary_partition_transport Data hd hs i r
      (piece r i) (theta i) (hSupport' i) (fun a => (hLift r i a).2.2) (hPart r i) z hz
    count := fun r i z => round3_prepared_parameter_secondary_count_transport Data hd hs i r
      (piece r i) (theta i) (hSupport' i) (fun a => (hLift r i a).2.2)
      (5^Module.finrank ℝ (Ep × D)) (hCount r i) z }⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_actual_parameter_secondary_pieces
