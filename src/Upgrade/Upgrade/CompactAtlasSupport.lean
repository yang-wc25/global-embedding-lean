import Upgrade.ProbeInterface
import Mathlib.Topology.ShrinkingLemma

/-!
# Enlarging the original supports for actual open incidence neighborhoods

The raw atlas does not relate inner domains to supports. Native finite open
shrinking gives compact closures inside the existing smooth chart sources.
Adjoining those closures to the old supports gives an interior support cover,
without changing charts, inner domains, or their original buffer. The original
atlas norm is bounded by the enlarged one. No coloring or initialization is
constructed here.
-/

noncomputable section
open Set Bundle Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade

/-- Monotonicity in the literal norm-evaluation domain, with the original
open differentiation domain and coordinate partials left unchanged. -/
theorem paperCoordinateCj_mono_evaluation_domain {n N : ℕ} (j : ℕ)
    (f : (Fin n → ℝ) → Fin N → ℝ) (O : Set (Fin n → ℝ))
    {S T : Set (Fin n → ℝ)} (hST : S ⊆ T) :
    paperCoordinateCj j f O S ≤ paperCoordinateCj j f O T := by
  unfold paperCoordinateCj
  refine iSup_le fun l ↦ iSup_le fun x ↦ iSup_le fun c ↦ ?_
  exact le_iSup_of_le l (le_iSup_of_le ⟨x, hST x.property⟩ (le_iSup_of_le c le_rfl))

variable {n N : ℕ} {M : Type*}
  [TopologicalSpace M] [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]

local notation "E" => EuclideanSpace ℝ (Fin n)
local notation "V" => EuclideanSpace ℝ (Fin N)

/-- Change only the separately specified support sets of the fixed atlas. -/
def enlargeBufferedAtlasSupport (A : BufferedAtlas M E) (S : Fin A.count → Set M) :
    BufferedAtlas M E := { A with support := S }

/-- Enlarging norm supports can only increase the original paper atlas gauge. -/
theorem probeAtlasCj_le_enlarged_support
    (A : BufferedAtlas M E) (S : Fin A.count → Set M)
    (hS : ∀ i, A.support i ⊆ S i) (j : ℕ) (f : M → V) :
    probeAtlasCj A j f ≤ probeAtlasCj (enlargeBufferedAtlasSupport A S) j f := by
  unfold probeAtlasCj paperAtlasCj
  apply iSup_le
  intro i
  apply le_iSup_of_le i
  apply paperCoordinateCj_mono_evaluation_domain
  exact image_mono (image_mono (hS i))

/-- Every finite smooth buffered atlas with compact original supports admits
compact enlarged supports whose interiors cover the entire closed manifold.
The same charts and original norm are retained, with a proved norm inequality.
This discharges the internal atlas hypothesis needed by local probe response
neighborhoods rather than adding a hypothesis to the original upgrade target. -/
theorem exists_compact_enlarged_support_cover [CompactSpace M] [T2Space M]
    (A : BufferedAtlas M E) (hA : IsSmoothBufferedAtlas A)
    (hcompact : ∀ i, IsCompact (A.support i)) :
    ∃ S : Fin A.count → Set M,
      (∀ i, A.support i ⊆ S i) ∧ (∀ i, IsCompact (S i)) ∧
      (∀ i, S i ⊆ (A.chart i).source) ∧
      (∀ x, ∃ i, x ∈ interior (S i)) ∧
      IsSmoothBufferedAtlas (enlargeBufferedAtlasSupport A S) ∧
      (∀ (j : ℕ) (f : M → V),
        probeAtlasCj A j f ≤ probeAtlasCj (enlargeBufferedAtlasSupport A S) j f) := by
  have hcover : (univ : Set M) ⊆ ⋃ i, A.inner i := by
    intro x _
    obtain ⟨i, hi⟩ := A.cover x
    exact mem_iUnion.mpr ⟨i, hi⟩
  obtain ⟨U, hUcover, hUopen, hUsub⟩ := exists_subset_iUnion_closure_subset
    isClosed_univ A.inner_open (fun _ _ ↦ Set.toFinite _) hcover
  let S : Fin A.count → Set M := fun i ↦ A.support i ∪ closure (U i)
  have hAS : ∀ i, A.support i ⊆ S i := fun _ _ hx ↦ Or.inl hx
  have hsource : ∀ i, S i ⊆ (A.chart i).source := by
    intro i x hx
    rcases hx with hx | hx
    · exact hA.support_subset i hx
    · exact A.inner_subset i (hUsub i hx)
  refine ⟨S, hAS, fun i ↦ (hcompact i).union isClosed_closure.isCompact,
    hsource, ?_, ⟨hA.chart_mem, hsource⟩,
    fun j f ↦ probeAtlasCj_le_enlarged_support A S hAS j f⟩
  intro x
  obtain ⟨i, hxi⟩ := mem_iUnion.mp (hUcover (mem_univ x))
  exact ⟨i, interior_maximal (fun z hz ↦ Or.inr (subset_closure hz)) (hUopen i) hxi⟩

end GlobalEmbedding.Upgrade
