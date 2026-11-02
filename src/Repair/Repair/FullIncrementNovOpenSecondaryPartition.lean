import Repair.FullIncrementNovOpenSecondaryRaw
import Probes.Round3PreparedParameterSecondaryStablePartition

/-! The actual signed packet partitions every original two-primary support
intersection on one genuine parameter neighborhood. All boundary support
points are included, and the overlap bound is the product of the original
parent count and the dimensional refinement count. No global partition on
parameters outside the original open set is imposed.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
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

theorem fullIncrementNov_secondary_local_partition_count
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (theta : (Fin Data.atlas.count × Fin Data.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Data hd hs theta)
    (V : Set P) (hPart : ∀ z : P × M, z.1 ∈ V → ∑ i, theta i z = 1) (L : ℕ)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (G : Set (P × M)) (hG : IsOpen G) (hGV : ∀ z ∈ G, z.1 ∈ V)
    (observer : Fin Data.parameterCount) (host : Fin Data.atlas.count) :
    let Sub := fun r => Sigma (fun i : Fin Data.atlas.count × Fin Data.parameterCount => ↥(packet.s r i))
    let physical := fun r (a : Sub r) => round3PreparedParameterSecondaryChoice Data hd hs a.1 r _ (packet.piece r a.1 a.2)
    let choice := fun r a => ((physical r a).pullback (Data.parameterChart observer)).toNative
    let W := round3ParameterNativeDomain (Data.parameterChart observer) G
    (∀ r y, y ∈ actualOriginalParameterSupportPair Data (host,observer) r.val.1.1 r.val.1.2 W →
      ∑ a : Sub r, (choice r a).cutoff y = 1) ∧
    (∀ r y, (Finset.univ.filter (fun a : Sub r => y ∈ tsupport (choice r a).cutoff ∩
      actualOriginalParameterSupportPair Data (host,observer) r.val.1.1 r.val.1.2 W)).card ≤
      L*(5^Module.finrank ℝ (Ep × D))) := by
  intro Sub physical choice W
  let U := (Data.parameterChart observer).target ×ˢ (univ : Set M)
  have hW : IsOpen W := round3Parameter_nativeDomain_open _ _ hG
  have hU : IsOpen U := (Data.parameterChart observer).open_target.prod isOpen_univ
  have hPair (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (y : Ep × M)
      (hy : y ∈ actualOriginalParameterSupportPair Data (host,observer) r.val.1.1 r.val.1.2 W) :
      y ∈ W ∧ y ∈ actualOriginalParameterSupportPair Data (host,observer) r.val.1.1 r.val.1.2 U := by
    simp only [actualOriginalParameterSupportPair,
      parameterRound2_global_relativeSupport_eq W hW,mem_inter_iff] at hy
    refine ⟨hy.1.1,?_⟩
    simp only [actualOriginalParameterSupportPair,
      parameterRound2_global_relativeSupport_eq U hU,mem_inter_iff]
    exact ⟨⟨⟨hy.1.1.1,mem_univ _⟩,hy.1.2⟩,⟨⟨hy.1.1.1,mem_univ _⟩,hy.2.2⟩⟩
  have hPhysicalCount (r) (z : P × M) :
      (Finset.univ.filter (fun a : Sub r => z ∈ round3PreparedParameterSecondaryCarrier Data r (physical r a))).card ≤
        L*(5^Module.finrank ℝ (Ep × D)) := by
    apply round3_prepared_sigma_local_count (fun i => ↥(packet.s r i))
      (fun i => tsupport (theta i))
      (fun i a => round3PreparedParameterSecondaryCarrier Data r (physical r ⟨i,a⟩))
      (fun i a _ hz => packet.parent r i a hz.1) L _ z (hCount z)
    exact fun i => packet.count r i z
  constructor
  · intro r y hy
    have hp := hPair r y hy
    have hP := round3_prepared_parameter_secondary_pair_physical Data (host,observer) r y hp.2
    change (∑ a : Sub r, (physical r a).cutoff ((Data.parameterChart observer).symm y.1,y.2)) = 1
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ i, theta i ((Data.parameterChart observer).symm y.1,y.2) := by
        apply Finset.sum_congr rfl
        intro i hi
        exact packet.partition r i _ hP.2
      _ = 1 := hPart _ (hGV _ hp.1.2)
  · intro r y
    apply (Finset.card_le_card ?_).trans (hPhysicalCount r ((Data.parameterChart observer).symm y.1,y.2))
    intro a ha
    have hy := (Finset.mem_filter.mp ha).2
    have hP := round3_prepared_parameter_secondary_pair_physical Data (host,observer) r y (hPair r y hy.2).2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,hP.2⟩
    exact (round3_prepared_native_tsupport_iff (round3ParameterProductChart (M := M) (Data.parameterChart observer))
      (physical r a).cutoff y ⟨hP.1,mem_univ _⟩).mp hy.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.fullIncrementNov_secondary_local_partition_count
