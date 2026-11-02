import Probes.Round3ParameterWholePrimaryPieces

/-! Actual primary pieces for a compact parameter set inside its original
open neighborhood.  The original parent cutoff is supported in that open
neighborhood, so the actual local refinement is performed there.  Only the
domain annotation is then enlarged; every chart, inverse, slice, cutoff and
primitive field is retained.  The ordinary partition germ and dimensional
overlap bound are proved on the unchanged physical supports.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
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

def fullIncrementNovPrimaryPieceEnlarge
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W U : Set (Ep × M))
    (piece : Round3PreparedPrimaryPiece Data ip nu W) (hWU : W ⊆ U) :
    Round3PreparedPrimaryPiece Data ip nu U where
  host := piece.host
  native := piece.native
  slices := piece.slices
  cutoff := piece.cutoff
  data := piece.data
  native_source := piece.native_source
  source_domain := fun z hz => hWU (piece.source_domain hz)
  active := piece.active
  compact := piece.compact
  smooth := piece.smooth
  support := piece.support
  Bnative := piece.Bnative
  positive := piece.positive
  native_first := piece.native_first

theorem fullIncrementNov_local_primary_partition_transport
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    {Sub : Type*} [Fintype Sub] (W G : Set (Ep × M)) (hG : IsOpen G)
    (piece : Sub → Round3PreparedPrimaryPiece Data ip nu W)
    (theta : P × M → ℝ)
    (hSupport : tsupport theta ⊆ (Data.parameterChart ip).source ×ˢ (univ : Set M))
    (hLocal : ∀ z ∈ tsupport theta, ((Data.parameterChart ip) z.1,z.2) ∈ G)
    (hGlobal : ∀ a, tsupport (round3ParameterLiftedPrimaryCutoff Data ip nu W (piece a)) ⊆ tsupport theta)
    (hGerm : ∀ y ∈ incrementsGlobalRelativeSupport G
      (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart ip).symm z.1,z.2)),
      ∀ᶠ w in 𝓝 y, ∑ a, (piece a).cutoff w = round3ParameterNativeParent (Data.parameterChart ip) theta w)
    (z : P × M) (hz : z ∈ tsupport (Data.cutoff nu)) :
    ∀ᶠ w in 𝓝 z, ∑ a, round3ParameterLiftedPrimaryCutoff Data ip nu W (piece a) w = theta w := by
  let q := round3ParameterProductChart (M := M) (Data.parameterChart ip)
  by_cases hzC : z ∈ tsupport theta
  · have hqs : z ∈ q.source := hSupport hzC
    have hTarget : q z ∈ incrementsGlobalRelativeSupport G
        (fun w : Ep × M => Data.cutoff nu ((Data.parameterChart ip).symm w.1,w.2)) := by
      rw [parameterRound2_global_relativeSupport_eq G hG]
      exact ⟨hLocal z hzC,round3Parameter_native_tsupport q (Data.cutoff nu) z hqs hz⟩
    have hc : Tendsto q (𝓝 z) (𝓝 (q z)) :=
      q.continuousOn.continuousAt (q.open_source.mem_nhds hqs)
    have hg := hc.eventually (hGerm (q z) hTarget)
    filter_upwards [hg,q.open_source.mem_nhds hqs] with w hw hws
    simp only [round3ParameterLiftedPrimaryCutoff_eq,ite_eq_left hws.1]
    change (∑ a, (piece a).cutoff (q w)) = theta w
    exact hw.trans (round3ParameterNativeParent_eq (Data.parameterChart ip) theta w hws.1)
  · filter_upwards [(isClosed_tsupport theta).isOpen_compl.mem_nhds hzC] with w hw
    rw [image_eq_zero_of_notMem_tsupport hw]
    exact Finset.sum_eq_zero (fun a _ =>
      image_eq_zero_of_notMem_tsupport (fun ha => hw (hGlobal a ha)))

variable [T2Space M]

theorem fullIncrementNov_original_open_primary_pieces
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    Nonempty (Round3ParameterWholePrimaryPieceSupply Data theta) := by
  let W := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    ((Data.parameterChart i.2).target ∩ (Data.parameterChart i.2).symm ⁻¹' Data.parameterOpen) ×ˢ
      (univ : Set M)
  let U := fun i : Fin Data.atlas.count × Fin Data.parameterCount =>
    (Data.parameterChart i.2).target ×ˢ (univ : Set M)
  have hW (i : Fin Data.atlas.count × Fin Data.parameterCount) : IsOpen (W i) :=
    ((Data.parameterChart i.2).symm.continuousOn.isOpen_inter_preimage
      (Data.parameterChart i.2).open_target hd.parameter_open).prod isOpen_univ
  have hSupport' (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M) :=
    fun z hz => ⟨(hSupport i hz).1.1,mem_univ _⟩
  have hLocal (i : Fin Data.atlas.count × Fin Data.parameterCount) (z : P × M)
      (hz : z ∈ tsupport (theta i)) : ((Data.parameterChart i.2) z.1,z.2) ∈ W i := by
    have hs := hSupport i hz
    refine ⟨⟨(Data.parameterChart i.2).map_source hs.1.1,?_⟩,mem_univ _⟩
    change (Data.parameterChart i.2).symm ((Data.parameterChart i.2) z.1) ∈ Data.parameterOpen
    rw [(Data.parameterChart i.2).left_inv hs.1.1]
    exact hs.1.2
  have hNative (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3Parameter_native_compact_parent (Data.parameterChart i.2)
      (hd.parameter_charts_smooth i.2) (theta i) (hCompact i) (hSmooth i) (hSupport' i)
  have hNSupport (i : Fin Data.atlas.count × Fin Data.parameterCount) :
      tsupport (round3ParameterNativeParent (Data.parameterChart i.2) (theta i)) ⊆
        W i ∩ (actualOriginalHostJointChart («Ep» := Ep) (Data.atlas.chart i.1)).source := by
    intro y hy
    obtain ⟨z,hz,rfl⟩ := (hNative i).2.2 hy
    exact ⟨hLocal i z hz,mem_univ _,Data.atlas.inner_subset i.1 (hSupport i hz).2⟩
  have hPieces (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round3_actual_original_primary_pieces Data hd hs hp i nu (W i) (hW i)
      (fun _ hy => hy.1.1) (fun z hz => ⟨hz.1.2,mem_univ _⟩)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i)
  choose s piece hHost hParent hGerm hCount using hPieces
  let out := fun nu i (a : s nu i) => fullIncrementNovPrimaryPieceEnlarge Data i.2 nu (W i) (U i)
    (piece nu i a) (fun _ hz => ⟨hz.1.1,hz.2⟩)
  have hLift (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s nu i) :=
    round3Parameter_original_primary_cutoff Data hd i.2 nu (U i) (out nu i a)
      (theta i) (hCompact i) (hSupport' i) (hNative i).2.2 (hParent nu i a)
  exact ⟨{
    s := s
    piece := out
    host := hHost
    native_parent := hParent
    smooth := fun nu i a => (hLift nu i a).1
    compact := fun nu i a => (hLift nu i a).2.1
    parent := fun nu i a => (hLift nu i a).2.2.1
    source := fun nu i a => (hLift nu i a).2.2.2
    partition := fun nu i z hz => fullIncrementNov_local_primary_partition_transport Data i.2 nu
      (U i) (W i) (hW i) (out nu i) (theta i) (hSupport' i) (hLocal i)
      (fun a => (hLift nu i a).2.2.1) (hGerm nu i) z hz
    count := fun nu i z => round3Parameter_primary_count_transport Data i.2 nu (U i)
      (out nu i) (theta i) (hSupport' i) (fun a => (hLift nu i a).2.2.1)
      (5^Module.finrank ℝ (Ep × D)) (hCount nu i) z }⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.fullIncrementNovPrimaryPieceEnlarge
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_local_primary_partition_transport
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_original_open_primary_pieces
