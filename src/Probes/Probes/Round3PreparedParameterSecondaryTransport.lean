import Probes.Round3PreparedParameterSecondaryLift
import Probes.Round3ParameterPrimaryPartitionTransport

/-! The full two-primary support intersection, including zero boundary
points, transports to the effective signed carrier. Ordinary secondary
partitions and the true local carrier count survive the single physical
choice construction. -/
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

 def round3PreparedParameterSecondaryCarrier
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (choice : Round3ParameterSecondaryChoice P M m) : Set (P × M) :=
    tsupport choice.cutoff ∩ (tsupport (Data.cutoff r.val.1.1) ∩ tsupport (Data.cutoff r.val.1.2))

 theorem round3_prepared_parameter_secondary_pair_native
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (z : P × M) (hz : z.1 ∈ (Data.parameterChart i.2).source)
    (hPair : z ∈ tsupport (Data.cutoff r.val.1.1) ∩ tsupport (Data.cutoff r.val.1.2)) :
    ((Data.parameterChart i.2) z.1,z.2) ∈ actualOriginalParameterSupportPair Data i
      r.val.1.1 r.val.1.2 ((Data.parameterChart i.2).target ×ˢ (univ : Set M)) := by
  let q := round3ParameterProductChart (M := M) (Data.parameterChart i.2)
  have hq : z ∈ q.source := ⟨hz,mem_univ _⟩
  have hOne (nu) (hn : z ∈ tsupport (Data.cutoff nu)) :
      q z ∈ incrementsGlobalRelativeSupport ((Data.parameterChart i.2).target ×ˢ (univ : Set M))
        (fun w : Ep × M => Data.cutoff nu ((Data.parameterChart i.2).symm w.1,w.2)) := by
    rw [parameterRound2_global_relativeSupport_eq _ ((Data.parameterChart i.2).open_target.prod isOpen_univ)]
    exact ⟨q.map_source hq,round3Parameter_native_tsupport q (Data.cutoff nu) z hq hn⟩
  exact ⟨hOne _ hPair.1,hOne _ hPair.2⟩

 theorem round3_prepared_parameter_secondary_carrier_source
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    (piece : Round3PreparedSignedReferencePiece Data hd hs i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)))
    (theta : P × M → ℝ)
    (hSupport : tsupport theta ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hParent : tsupport (round3PreparedParameterSecondaryChoice Data hd hs i r _ piece).cutoff ⊆ tsupport theta) :
    let choice := round3PreparedParameterSecondaryChoice Data hd hs i r _ piece
    round3PreparedParameterSecondaryCarrier Data r choice ⊆ choice.chart.source ∧
    MapsTo (round3ParameterProductChart (Data.parameterChart i.2))
      (round3PreparedParameterSecondaryCarrier Data r choice) piece.carrier := by
  intro choice
  let q := round3ParameterProductChart (M := M) (Data.parameterChart i.2)
  have hNative (z) (hz : z ∈ round3PreparedParameterSecondaryCarrier Data r choice) : q z ∈ piece.carrier := by
    have hqs : z ∈ q.source := hSupport (hParent hz.1)
    rw [piece.carrier_eq]
    exact ⟨(round3ParameterSupportedPullback_tsupport_iff q piece.cutoff z hqs).mp hz.1,
      round3_prepared_parameter_secondary_pair_native Data i r z hqs.1 hz.2⟩
  refine ⟨?_,hNative⟩
  intro z hz
  have hqs : z ∈ q.source := hSupport (hParent hz.1)
  apply (round3ParameterChartPullback_source_iff (Data.parameterChart i.2).symm
    (actualHostAdaptedChart (Data.atlas.chart i.1) piece.native)
    (fun y hy => (piece.data.2.2.2.1 y hy).1) z hqs.1).mpr
  exact piece.carrier_source (hNative z hz)

 theorem round3_prepared_parameter_secondary_partition_transport
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    {A : Type*} [Fintype A]
    (piece : A → Round3PreparedSignedReferencePiece Data hd hs i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)))
    (theta : P × M → ℝ)
    (hSupport : tsupport theta ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hParent : ∀ a, tsupport (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece a)).cutoff ⊆ tsupport theta)
    (hPart : ∀ y ∈ actualOriginalParameterSupportPair Data i r.val.1.1 r.val.1.2
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)),
      ∑ a, (piece a).cutoff y = round3ParameterNativeParent (Data.parameterChart i.2) theta y)
    (z : P × M) (hz : z ∈ tsupport (Data.cutoff r.val.1.1) ∩ tsupport (Data.cutoff r.val.1.2)) :
    ∑ a, (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece a)).cutoff z = theta z := by
  by_cases hzs : z.1 ∈ (Data.parameterChart i.2).source
  · have hqs : z ∈ (round3ParameterProductChart (M := M) (Data.parameterChart i.2)).source := ⟨hzs,mem_univ _⟩
    have he := hPart ((Data.parameterChart i.2) z.1,z.2)
      (round3_prepared_parameter_secondary_pair_native Data i r z hzs hz)
    simp only [round3PreparedParameterSecondaryChoice,round3ParameterSupportedPullback,if_pos hqs]
    exact he.trans (round3ParameterNativeParent_eq (Data.parameterChart i.2) theta z hzs)
  · have hzC : z ∉ tsupport theta := fun hz => hzs (hSupport hz).1
    rw [image_eq_zero_of_notMem_tsupport hzC]
    exact Finset.sum_eq_zero (fun a _ => image_eq_zero_of_notMem_tsupport (fun ha => hzC (hParent a ha)))

 theorem round3_prepared_parameter_secondary_count_transport
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (hd : IncrementsOriginalDomainConditions Data) (hs : IncrementsOriginalSmoothInputs Data)
    (i : Fin Data.atlas.count × Fin Data.parameterCount)
    (r : ActualSecondarySignedRecord (Fin Data.primaryCount))
    {A : Type*} [Fintype A]
    (piece : A → Round3PreparedSignedReferencePiece Data hd hs i r
      ((Data.parameterChart i.2).target ×ˢ (univ : Set M)))
    (theta : P × M → ℝ)
    (hSupport : tsupport theta ⊆ (Data.parameterChart i.2).source ×ˢ (univ : Set M))
    (hParent : ∀ a, tsupport (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece a)).cutoff ⊆ tsupport theta)
    (R : ℕ) (hCount : ∀ y, (Finset.univ.filter (fun a => y ∈ (piece a).carrier)).card ≤ R)
    (z : P × M) :
    (Finset.univ.filter (fun a => z ∈ round3PreparedParameterSecondaryCarrier Data r
      (round3PreparedParameterSecondaryChoice Data hd hs i r _ (piece a)))).card ≤ R := by
  apply (Finset.card_le_card ?_).trans (hCount ((Data.parameterChart i.2) z.1,z.2))
  intro a ha
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (round3_prepared_parameter_secondary_carrier_source Data hd hs i r (piece a) theta
      hSupport (hParent a)).2 (Finset.mem_filter.mp ha).2⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_partition_transport
#print axioms GlobalEmbedding.Continuation.round3_prepared_parameter_secondary_count_transport
