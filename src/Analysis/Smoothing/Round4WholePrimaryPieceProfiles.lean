import Probes.Round3ParameterWholePrimaryPieces
import Smoothing.Round4PrimaryPieceProfiles

/-! Genuine finite primary pieces over ALL original parameter charts on a
whole-parameter repair stage. Every native piece is constructed from the
original phase, and every transported cutoff has its real global support,
ordinary germ partition, and dimensional overlap bound. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

variable [T2Space M]
set_option backward.isDefEq.respectTransparency true in
theorem round4Parameter_actual_whole_primary_pieces_profiles
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (hp : IncrementsOriginalPhaseConditions Data hd hs) (hAll : Data.parameterSet = univ)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (hCompact : ∀ i, IsCompact (tsupport (theta i)))
    (hSmooth : ∀ i, ContMDiff ((𝓘(ℝ,Ep)).prod 𝓙) 𝓘(ℝ,ℝ) ∞ (theta i))
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Data.parameterChart i.2).source ×ˢ Data.atlas.inner i.1) :
    ∃ packet : Round3ParameterWholePrimaryPieceSupply Data theta,
      ∀ nu i, Nonempty (Round4PrimaryJetSupply Data i nu
        ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
        (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
        (packet.s nu i) (packet.piece nu i)) := by
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
  have hLocal (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) :=
    round4_actual_original_primary_pieces_profiles Data hd hs hp i nu (W i) (hW i)
      (fun _ hy => hy.1) (fun z _ => ⟨hOpen _,mem_univ _⟩)
      (round3ParameterNativeParent (Data.parameterChart i.2) (theta i))
      (hNative i).2.1 (hNative i).1 (hNSupport i)
  choose s piece hHost hParent hGerm hCount hJets using hLocal
  have hLift (nu : Fin Data.primaryCount) (i : Fin Data.atlas.count × Fin Data.parameterCount) (a : s nu i) := round3Parameter_original_primary_cutoff Data hd i.2 nu (W i)
    (piece nu i a) (theta i) (hCompact i) (hSupport' i) (hNative i).2.2 (hParent nu i a)
  let packet : Round3ParameterWholePrimaryPieceSupply Data theta := {
    s := s
    piece := piece
    host := hHost
    native_parent := hParent
    smooth := fun nu i a => (hLift nu i a).1
    compact := fun nu i a => (hLift nu i a).2.1
    parent := fun nu i a => (hLift nu i a).2.2.1
    source := fun nu i a => (hLift nu i a).2.2.2
    partition := fun nu i z hz => round3Parameter_primary_partition_transport Data i.2 nu
      (piece nu i) (theta i) (hSupport' i) (fun a => (hLift nu i a).2.2.1) (hGerm nu i) z hz
    count := fun nu i z => round3Parameter_primary_count_transport Data i.2 nu (W i)
      (piece nu i) (theta i) (hSupport' i) (fun a => (hLift nu i a).2.2.1)
      (5^Module.finrank ℝ (Ep × D)) (hCount nu i) z }
  exact ⟨packet,hJets⟩

#print axioms round4Parameter_actual_whole_primary_pieces_profiles
end GlobalEmbedding.Continuation
