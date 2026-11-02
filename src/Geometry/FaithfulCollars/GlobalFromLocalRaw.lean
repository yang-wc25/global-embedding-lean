import FaithfulCollars.OriginalCompactRawPair

/-!
# Promote an actual global plateau cover without changing its functions

When the prescribed parameter set is `univ`, its manufactured local raw
preparation supplies a genuine finite buffered atlas.  The internal graph
supports are clipped to their original chart sources.  This changes no
raw function and can only decrease the original intersection degrees.
-/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Metric Manifold IsManifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.FaithfulCollars

theorem enlargedSupportDegree_mono
    {ι X : Type*} [Fintype ι] [TopologicalSpace X]
    (V W : ι → Set X) (h : ∀ i, V i ⊆ W i) (i : ι) :
    tensorEnlargedSupportDegree V i ≤ tensorEnlargedSupportDegree W i := by
  classical
  apply Finset.card_le_card
  intro j hj
  have hij := ((tensorEnlargedSupportGraph V).mem_neighborFinset i j).mp hj
  apply ((tensorEnlargedSupportGraph W).mem_neighborFinset i j).mpr
  obtain ⟨hne, x, hxi, hxj⟩ := hij
  exact ⟨hne, x, h i hxi, h j hxj⟩

variable {c : ℕ} {E P : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace P] [ChartedSpace E P] [IsManifold 𝓘(ℝ,E) ∞ P]
  {A : TensorBufferedChartFamily (Fin c) P E} {B T : ℕ → ℝ} {D : ℕ}

def globalAtlasOfLocalRaw (R : TensorLocalRawPreparation A univ B T D) : BufferedAtlas P E where
  count := c
  chart := A.chart
  inner := A.inner
  inner_open := A.inner_open
  inner_subset := A.inner_subset
  cover p := by
    obtain ⟨i, hi⟩ := R.plateau_on p (mem_univ p)
    refine ⟨i, R.inner_support i (subset_tsupport (R.raw i) ?_)⟩
    change R.raw i p ≠ 0
    rw [hi]
    exact one_ne_zero
  buffer := A.buffer
  buffer_pos := A.buffer_pos
  buffered := A.buffered
  support i := R.enlarged i ∩ (A.chart i).source

theorem globalAtlasOfLocalRaw_smooth
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ,E) ∞ P)
    (R : TensorLocalRawPreparation A univ B T D) :
    IsSmoothBufferedAtlas (globalAtlasOfLocalRaw R) :=
  ⟨hA, fun _ => inter_subset_right⟩

theorem globalAtlasOfLocalRaw_degree (R : TensorLocalRawPreparation A univ B T D) :
    (globalAtlasOfLocalRaw R).supportDegree ≤ D := by
  classical
  apply Finset.sup_le
  intro i _
  change tensorEnlargedSupportDegree (globalAtlasOfLocalRaw R).support i ≤ D
  exact (enlargedSupportDegree_mono _ R.enlarged (fun _ => inter_subset_left) i).trans (R.degree i)

/-- Every computational field is the given actual local raw function or
chart.  No new covering function or derivative estimate is postulated. -/
def globalRawPreparationOfLocal (R : TensorLocalRawPreparation A univ B T D) :
    TensorRawCutoffPreparation (globalAtlasOfLocalRaw R) B T D where
  raw := R.raw
  smooth := R.smooth
  plateau_cover := fun p => R.plateau_on p (mem_univ p)
  inner_support := R.inner_support
  enlarged_support := fun i p hp => ⟨R.enlarged_support i hp,
    A.inner_subset i (R.inner_support i hp)⟩
  degree := globalAtlasOfLocalRaw_degree R
  own_jets := R.own_jets
  transition_jets := R.transition_jets

theorem globalRawPreparationOfLocal_original_fields
    (R : TensorLocalRawPreparation A univ B T D) :
    (globalAtlasOfLocalRaw R).chart = A.chart ∧
    (globalAtlasOfLocalRaw R).inner = A.inner ∧
    (globalAtlasOfLocalRaw R).buffer = A.buffer ∧
    (globalRawPreparationOfLocal R).raw = R.raw ∧
    (∀ i, (globalAtlasOfLocalRaw R).support i ⊆ R.enlarged i) :=
  ⟨rfl, rfl, rfl, rfl, fun _ => inter_subset_left⟩

end GlobalEmbedding.Continuation.FaithfulCollars

#print axioms GlobalEmbedding.Continuation.FaithfulCollars.globalRawPreparationOfLocal
#print axioms GlobalEmbedding.Continuation.FaithfulCollars.enlargedSupportDegree_mono
