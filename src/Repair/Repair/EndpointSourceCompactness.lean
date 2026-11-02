import Smoothing.Round3RepairCurrentState

/-! Compactness of the original source follows from the finite actual
buffered sampling cover and its compact coordinate norm domains.  A public
repair theorem using this material need not assume a second closed-source
hypothesis.  Empty atlases and empty sources are covered by the same proof. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set
namespace GlobalEmbedding.Continuation

theorem repair_source_compact_of_original_sampling
    {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace M]
    (A : BufferedAtlas M E) (Omega : Fin A.count → Set E)
    (hCompact : ∀ i, IsCompact (Omega i))
    (hTarget : ∀ i, Omega i ⊆ (A.chart i).target)
    (hSampling : ∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) :
    CompactSpace M := by
  have hImage (i : Fin A.count) : IsCompact ((A.chart i).symm '' Omega i) :=
    (hCompact i).image_of_continuousOn ((A.chart i).continuousOn_symm.mono (hTarget i))
  have hCover : (⋃ i, (A.chart i).symm '' Omega i) = (univ : Set M) := by
    apply eq_univ_of_forall
    intro x
    obtain ⟨i,hi⟩ := A.cover x
    apply mem_iUnion.mpr
    refine ⟨i, A.chart i x, ?_, (A.chart i).left_inv (A.inner_subset i hi)⟩
    apply hSampling i
    apply bufferedInner_subset_sampling A i
    exact ⟨(A.chart i).map_source (A.inner_subset i hi), by
      change (A.chart i).symm (A.chart i x) ∈ A.inner i
      simpa only [(A.chart i).left_inv (A.inner_subset i hi)] using hi⟩
  exact ⟨hCover ▸ isCompact_iUnion hImage⟩

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.repair_source_compact_of_original_sampling
