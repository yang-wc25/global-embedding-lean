import FaithfulRepair.OriginalJetFiniteness

/-! One actual compact core family, chosen before every derivative order,
for arbitrary local coordinate representatives.  This is shared by native
tensor and dual-tensor transport.  It uses the physical compact observation
set and its given chart cover, never compactifies the original samples. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff Topology
namespace GlobalEmbedding.Continuation.FaithfulRepair

variable {E F X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X] [R1Space X] [Fintype ι]

/-- Compact coordinate cores and every finite jet bound are manufactured
from the actual smooth coordinate family and the compact physical set.
The same cores work for every order. -/
theorem original_compact_family_jet_cores
    (chart : ι → OpenPartialHomeomorph X E)
    (K W : Set X) (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hCover : ∀ x ∈ K, ∃ i, x ∈ (chart i).source)
    (f : ι → E → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f i) ((chart i).target ∩ (chart i).symm ⁻¹' W)) :
    ∃ core : ι → Set X, (∀ i, IsCompact (core i)) ∧
      (∀ i, core i ⊆ (chart i).source ∩ W) ∧ K = ⋃ i, core i ∧
      ∀ j : ℕ, ∃ R : ℝ, 0 ≤ R ∧ ∀ i k, k ≤ j →
        ∀ y ∈ (chart i) '' core i, ‖iteratedFDeriv ℝ k (f i) y‖ ≤ R := by
  classical
  obtain ⟨core,hCompact,hSub,hCovered⟩ :=
    original_finite_chart_compact_cores chart K W hK hW hKW hCover
  refine ⟨core,hCompact,hSub,hCovered,?_⟩
  let V := fun i => (chart i).target ∩ (chart i).symm ⁻¹' W
  have hV : ∀ i, IsOpen (V i) := fun i =>
    (chart i).symm.continuousOn.isOpen_inter_preimage (chart i).open_target hW
  have hImageCompact : ∀ i, IsCompact ((chart i) '' core i) := fun i =>
    (hCompact i).image_of_continuousOn ((chart i).continuousOn.mono (fun _ hx => (hSub i hx).1))
  have hImageSub : ∀ i, (chart i) '' core i ⊆ V i := by
    intro i y hy
    obtain ⟨x,hx,rfl⟩ := hy
    refine ⟨(chart i).map_source (hSub i hx).1,?_⟩
    change (chart i).symm (chart i x) ∈ W
    rw [(chart i).left_inv (hSub i hx).1]
    exact (hSub i hx).2
  intro j
  have hEach : ∀ a : ι × Fin (j+1), ∃ R : ℝ,
      ∀ y ∈ (chart a.1) '' core a.1, ‖iteratedFDeriv ℝ (a.2 : ℕ) (f a.1) y‖ ≤ R := by
    intro a
    obtain ⟨R,hR⟩ := parameterRound2_coordinate_jets_bounded_of_compact (f a.1) (V a.1)
      ((chart a.1) '' core a.1) ((chart a.1) '' core a.1) (hV a.1) (hImageCompact a.1)
      Subset.rfl (hImageSub a.1) (hf a.1) a.2
    exact ⟨R,fun y hy => hR ⟨⟨y,hy⟩,rfl⟩⟩
  choose R hR using hEach
  obtain ⟨B,hB⟩ := (Set.finite_range R).bddAbove
  refine ⟨max 0 B,le_max_left _ _,?_⟩
  intro i k hk y hy
  let a : ι × Fin (j+1) := (i,⟨k,by omega⟩)
  exact (hR a y hy).trans ((hB (mem_range_self a)).trans (le_max_right _ _))

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_compact_family_jet_cores
