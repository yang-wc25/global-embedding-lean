import Probes.Round3ParameterPrimaryCarrier

/-! The actual ordinary primary partition is transported as a germ and its
local support count is preserved. This is stronger than pointwise sums and
is the identity consumed by the subsequent jet calculations. -/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Manifold IsManifold Filter
open scoped ContDiff Topology BigOperators Classical
namespace GlobalEmbedding.Continuation

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
theorem round3Parameter_native_tsupport
    (q : OpenPartialHomeomorph X Y) (f : X → ℝ) (x : X)
    (hx : x ∈ q.source) (hs : x ∈ tsupport f) :
    q x ∈ tsupport (fun y => f (q.symm y)) := by
  by_contra hn
  have hzero := (notMem_tsupport_iff_eventuallyEq.mp hn).comp_tendsto
    (q.continuousOn.continuousAt (q.open_source.mem_nhds hx))
  apply (notMem_tsupport_iff_eventuallyEq.mpr ?_) hs
  filter_upwards [hzero,q.open_source.mem_nhds hx] with y hy hys
  simpa only [Function.comp_apply,Pi.zero_apply,q.left_inv hys] using hy

variable {m d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin (m+1))) M]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) ∞ M]
  [BoundarylessManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin (m+1))) M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ,EuclideanSpace ℝ (Fin d)) ∞ P]
local notation "D" => EuclideanSpace ℝ (Fin (m+1))
local notation "Ep" => EuclideanSpace ℝ (Fin d)

theorem round3Parameter_primary_partition_transport
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount)
    {α : Type*} [Fintype α]
    (piece : α → Round3PreparedPrimaryPiece Data ip nu ((Data.parameterChart ip).target ×ˢ (univ : Set M)))
    (theta : P × M → ℝ)
    (hSupport : tsupport theta ⊆ (Data.parameterChart ip).source ×ˢ (univ : Set M))
    (hGlobal : ∀ a, tsupport (round3ParameterLiftedPrimaryCutoff Data ip nu _ (piece a)) ⊆ tsupport theta)
    (hGerm : ∀ y ∈ incrementsGlobalRelativeSupport ((Data.parameterChart ip).target ×ˢ (univ : Set M))
      (fun z : Ep × M => Data.cutoff nu ((Data.parameterChart ip).symm z.1,z.2)),
      ∀ᶠ w in 𝓝 y, ∑ a, (piece a).cutoff w = round3ParameterNativeParent (Data.parameterChart ip) theta w)
    (z : P × M) (hz : z ∈ tsupport (Data.cutoff nu)) :
    ∀ᶠ w in 𝓝 z, ∑ a, round3ParameterLiftedPrimaryCutoff Data ip nu _ (piece a) w = theta w := by
  let q := round3ParameterProductChart (M := M) (Data.parameterChart ip)
  by_cases hzs : z.1 ∈ (Data.parameterChart ip).source
  · have hqs : z ∈ q.source := ⟨hzs,mem_univ _⟩
    have hTarget : q z ∈ incrementsGlobalRelativeSupport ((Data.parameterChart ip).target ×ˢ (univ : Set M))
        (fun w : Ep × M => Data.cutoff nu ((Data.parameterChart ip).symm w.1,w.2)) := by
      rw [parameterRound2_global_relativeSupport_eq _ ((Data.parameterChart ip).open_target.prod isOpen_univ)]
      exact ⟨q.map_source hqs,round3Parameter_native_tsupport q (Data.cutoff nu) z hqs hz⟩
    have hc : Tendsto q (𝓝 z) (𝓝 (q z)) :=
      q.continuousOn.continuousAt (q.open_source.mem_nhds hqs)
    have hg := hc.eventually (hGerm (q z) hTarget)
    filter_upwards [hg,q.open_source.mem_nhds hqs] with w hw hws
    simp only [round3ParameterLiftedPrimaryCutoff_eq,ite_eq_left hws.1]
    change (∑ a, (piece a).cutoff (q w)) = theta w
    exact hw.trans (round3ParameterNativeParent_eq (Data.parameterChart ip) theta w hws.1)
  · have hzC : z ∉ tsupport theta := fun hz => hzs (hSupport hz).1
    filter_upwards [(isClosed_tsupport theta).isOpen_compl.mem_nhds hzC] with w hw
    rw [image_eq_zero_of_notMem_tsupport hw]
    exact Finset.sum_eq_zero (fun a _ => image_eq_zero_of_notMem_tsupport (fun ha => hw (hGlobal a ha)))

theorem round3Parameter_primary_count_transport
    (Data : IncrementsOriginalNativeData (m+1) d N M P)
    (ip : Fin Data.parameterCount) (nu : Fin Data.primaryCount) (W : Set (Ep × M))
    {α : Type*} [Fintype α] (piece : α → Round3PreparedPrimaryPiece Data ip nu W)
    (theta : P × M → ℝ)
    (hSupport : tsupport theta ⊆ (Data.parameterChart ip).source ×ˢ (univ : Set M))
    (hGlobal : ∀ a, tsupport (round3ParameterLiftedPrimaryCutoff Data ip nu W (piece a)) ⊆ tsupport theta)
    (R : ℕ) (hCount : ∀ y, (Finset.univ.filter (fun a => y ∈ tsupport (piece a).cutoff)).card ≤ R)
    (z : P × M) :
    (Finset.univ.filter (fun a => z ∈ tsupport (round3ParameterLiftedPrimaryCutoff Data ip nu W (piece a)))).card ≤ R := by
  let q := round3ParameterProductChart (M := M) (Data.parameterChart ip)
  apply (Finset.card_le_card ?_).trans (hCount (q z))
  intro a ha
  have hz := (Finset.mem_filter.mp ha).2
  have hqs : z ∈ q.source := hSupport (hGlobal a hz)
  exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,
    (round3ParameterSupportedPullback_tsupport_iff q (piece a).cutoff z hqs).mp hz⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.round3Parameter_primary_partition_transport
#print axioms GlobalEmbedding.Continuation.round3Parameter_primary_count_transport
