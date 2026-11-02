import Probes.Round3PreparedParameterSecondaryStableProfiles
import Probes.Round3PreparedParameterSecondaryNativeCarrier

/-! The actual whole-parameter signed family keeps the ordinary partition
and its genuine local overlap after current-map domain restriction. These
are the canonical native carriers, including zero boundary intersections. -/
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
local notation "Ey" => EuclideanSpace ℝ (Fin N)
local notation "𝓙" => 𝓘(ℝ,D)

 theorem round3_prepared_parameter_secondary_pair_physical
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount)) (y : Ep × M)
    (hy : y ∈ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M))) :
    y.1 ∈ (Data.parameterChart i.2).target ∧
      ((Data.parameterChart i.2).symm y.1,y.2) ∈
        tsupport (Data.cutoff r.val.1.1) ∩ tsupport (Data.cutoff r.val.1.2) := by
  let B := Data.parameterChart i.2
  let q := round3ParameterProductChart (M := M) B
  have hn := hy.1
  have hm := hy.2
  rw [parameterRound2_global_relativeSupport_eq _ (B.open_target.prod isOpen_univ)] at hn hm
  exact ⟨hn.1.1,(round3_prepared_native_tsupport_iff q (Data.cutoff r.val.1.1) y hn.1).mp hn.2,
    (round3_prepared_native_tsupport_iff q (Data.cutoff r.val.1.2) y hm.1).mp hm.2⟩

 theorem round3_prepared_parameter_secondary_stable_partition_count
    (Ref : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Ref) (hs : IncrementsOriginalSmoothInputs Ref)
    (theta : (Fin Ref.atlas.count × Fin Ref.parameterCount) → P × M → ℝ)
    (packet : Round3PreparedParameterSecondaryPacket Ref hd hs theta)
    (hSupport : ∀ i, tsupport (theta i) ⊆ (Ref.parameterChart i.2).source ×ˢ (univ : Set M))
    (hPart : ∀ z, ∑ i, theta i z = 1) (L : ℕ)
    (hCount : ∀ z, (Finset.univ.filter (fun i => z ∈ tsupport (theta i))).card ≤ L)
    (F : P → M → Ey) (hF : ∀ p, ContMDiff 𝓙 𝓘(ℝ,Ey) ∞ (F p))
    (stable : ∀ r i (a : packet.s r i), Round3PreparedParameterStableSecondaryPiece Ref hd hs i r _ (packet.piece r i a) F hF)
    (observer : Fin Ref.parameterCount) (host : Fin Ref.atlas.count) :
    let Sub := fun r => Sigma (fun i : Fin Ref.atlas.count × Fin Ref.parameterCount => ↥(packet.s r i))
    let physical := fun r (a : Sub r) => round3PreparedParameterSecondaryChoice Ref hd hs a.1 r _ (stable r a.1 a.2).piece
    let choice := fun r a => ((physical r a).pullback (Ref.parameterChart observer)).toNative
    let W := (Ref.parameterChart observer).target ×ˢ (univ : Set M)
    (∀ r y, y ∈ actualOriginalParameterSupportPair Ref (host,observer) r.val.1.1 r.val.1.2 W →
      ∑ a : Sub r, (choice r a).cutoff y = 1) ∧
    (∀ r y, (Finset.univ.filter (fun a : Sub r => y ∈ tsupport (choice r a).cutoff ∩
      actualOriginalParameterSupportPair Ref (host,observer) r.val.1.1 r.val.1.2 W)).card ≤
      L*(5^Module.finrank ℝ (Ep × D))) := by
  intro Sub physical choice W
  have hEqual (r) (i) (a : packet.s r i) :=
    (round3_prepared_parameter_secondary_stable_functions Ref hd hs i r _ (packet.piece r i a)
      F hF (stable r i a) observer).1
  have hParent (r) (i) (a : packet.s r i) :
      tsupport (physical r ⟨i,a⟩).cutoff ⊆ tsupport (theta i) := by
    change tsupport (round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece).cutoff ⊆ _
    rw [hEqual r i a]
    exact packet.parent r i a
  have hCarrierEqual (r) (i) (a : packet.s r i) :
      round3PreparedParameterSecondaryCarrier Ref r (physical r ⟨i,a⟩) =
      round3PreparedParameterSecondaryCarrier Ref r
        (round3PreparedParameterSecondaryChoice Ref hd hs i r _ (packet.piece r i a)) := by
    unfold round3PreparedParameterSecondaryCarrier
    rw [show (physical r ⟨i,a⟩).cutoff = _ from hEqual r i a]
  have hPhysicalCount (r) (z : P × M) :
      (Finset.univ.filter (fun a : Sub r => z ∈ round3PreparedParameterSecondaryCarrier Ref r (physical r a))).card ≤
        L*(5^Module.finrank ℝ (Ep × D)) := by
    apply round3_prepared_sigma_local_count (fun i => ↥(packet.s r i))
      (fun i => tsupport (theta i))
      (fun i a => round3PreparedParameterSecondaryCarrier Ref r (physical r ⟨i,a⟩))
      (fun i a _ hz => hParent r i a hz.1) L _ z (hCount z)
    intro i
    simp_rw [hCarrierEqual]
    exact packet.count r i z
  constructor
  · intro r y hy
    have hP := round3_prepared_parameter_secondary_pair_physical Ref (host,observer) r y hy
    change (∑ a : Sub r, (physical r a).cutoff ((Ref.parameterChart observer).symm y.1,y.2)) = 1
    rw [Fintype.sum_sigma]
    calc
      _ = ∑ i, theta i ((Ref.parameterChart observer).symm y.1,y.2) := by
        apply Finset.sum_congr rfl
        intro i hi
        change (∑ a : packet.s r i, (round3PreparedParameterSecondaryChoice Ref hd hs i r _ (stable r i a).piece).cutoff _) = _
        simp_rw [hEqual]
        exact packet.partition r i _ hP.2
      _ = 1 := hPart _
  · intro r y
    apply (Finset.card_le_card ?_).trans (hPhysicalCount r ((Ref.parameterChart observer).symm y.1,y.2))
    intro a ha
    have hy := (Finset.mem_filter.mp ha).2
    have hP := round3_prepared_parameter_secondary_pair_physical Ref (host,observer) r y hy.2
    refine Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_,hP.2⟩
    exact (round3_prepared_native_tsupport_iff (round3ParameterProductChart (M := M) (Ref.parameterChart observer))
      (physical r a).cutoff y ⟨hP.1,mem_univ _⟩).mp hy.1

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_stable_partition_count
