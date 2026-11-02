import Repair.FullIncrementNovOpenPrimaryPieces
import Smoothing.Round4PrimaryPieceProfiles

/-! The actual open-parameter primary construction retains the quantitative
jet certificate from the very same choice of native pieces.  Only the domain
annotation is enlarged, exactly as in the original open piece producer;
there is no all-parameter hypothesis or retrospective profile for arbitrary
previously chosen pieces. -/

noncomputable section
set_option backward.isDefEq.respectTransparency true
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P] [T2Space M]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "𝓙" => 𝓘(ℝ,D)

theorem auxBridgeNov_original_open_primary_pieces_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆
      ((Data.parameterChart i.2).source ∩ Data.parameterOpen) ×ˢ Data.atlas.inner i.1) :
    ∃ packet : Round3ParameterWholePrimaryPieceSupply Data theta,
      ∀ nu i, Nonempty (Round4PrimaryJetSupply Data i nu
        ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
        (packet.s nu i) (packet.piece nu i)) := by
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
    round4_actual_original_primary_pieces_profiles Data hd hs hp i nu (W i) (hW i)
      (fun _ hy => hy.1.1) (fun z hz => ⟨hz.1.2,mem_univ _⟩)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i)
  choose s piece hHost hParent hGerm hCount hJets using hPieces
  let out := fun nu i (a : s nu i) => fullIncrementNovPrimaryPieceEnlarge Data i.2 nu (W i) (U i)
    (piece nu i a) (fun _ hz => ⟨hz.1.1,hz.2⟩)
  have hLift (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s nu i) :=
    round3Parameter_original_primary_cutoff Data hd i.2 nu (U i) (out nu i a)
      (theta i) (hCompact i) (hSupport' i) (hNative i).2.2 (hParent nu i a)
  let packet : Round3ParameterWholePrimaryPieceSupply Data theta := {
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
      (5^Module.finrank ℝ (Ep × D)) (hCount nu i) z }
  refine ⟨packet,?_⟩
  intro nu i
  obtain ⟨jet⟩ := hJets nu i
  exact ⟨{
    mu := jet.mu
    Mb := jet.Mb
    buffer := jet.buffer
    O := jet.O
    mu_pos := jet.mu_pos
    Mb_nonneg := jet.Mb_nonneg
    buffer_pos := jet.buffer_pos
    open_domain := jet.open_domain
    domain := jet.domain
    source := jet.source
    jets := jet.jets }⟩

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.auxBridgeNov_original_open_primary_pieces_profiles
