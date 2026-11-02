import Smoothing.ParameterGeometryModel
import Smoothing.ParameterRound2CompactNorms
import Probes.Round3ParameterPrimaryChartSmooth
import Mathlib.Topology.Separation.Basic

/-!
# Original coordinate jets over a compact physical observation set

The parameter charts in the original statement cover the compact parameter
set, not necessarily the whole parameter manifold.  A finite compact cover
is manufactured inside these same charts.  Smoothness bounds the actual
input on that cover; the original positive-order transition estimates then
propagate the bounds to every point of the unchanged observation domains.

Neither compactness nor closedness of a coordinate observation domain is
assumed.  No higher-order numerical entrance budget is introduced.  This is
a qualitative finiteness producer for the same map and the same samples.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Manifold IsManifold Set Function Metric Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Continuation.FaithfulRepair

variable {E F X ι : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]
  [TopologicalSpace X] [R1Space X]
  [Fintype ι]

/-- The real coordinate cores are constructed from a finite chart cover of
the compact physical observation set.  Their union is exactly that set, and
each core stays inside both its actual chart and the given smooth region. -/
theorem original_finite_chart_compact_cores
    (chart : ι → OpenPartialHomeomorph X E)
    (K W : Set X) (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hCover : ∀ x ∈ K, ∃ i, x ∈ (chart i).source) :
    ∃ core : ι → Set X, (∀ i, IsCompact (core i)) ∧
      (∀ i, core i ⊆ (chart i).source ∩ W) ∧ K = ⋃ i, core i := by
  classical
  have hCovered : K ⊆ ⋃ i ∈ (Finset.univ : Finset ι), (chart i).source ∩ W := by
    intro x hx
    obtain ⟨i,hi⟩ := hCover x hx
    simp only [mem_iUnion]
    exact ⟨i, Finset.mem_univ i, hi, hKW hx⟩
  obtain ⟨core,hCompact,hSub,hEq⟩ := hK.finite_compact_cover Finset.univ
    (fun i => (chart i).source ∩ W) (fun i _ => (chart i).open_source.inter hW) hCovered
  refine ⟨core,hCompact,hSub,?_⟩
  simpa only [Finset.mem_univ, iUnion_true] using hEq

/-- A genuine all-order bound on the literal original coordinate samples.
The only numerical coordinate input is the original positive-order
transition profile.  The compact set is a physical set, not a replacement
for any coordinate norm domain. -/
theorem original_compact_observation_jet_profile_exists
    (chart : ι → OpenPartialHomeomorph X E)
    (hSmoothTransition : ∀ i j, ContDiffOn ℝ ∞ ((chart i).symm.trans (chart j))
      ((chart i).symm.trans (chart j)).source)
    (K W : Set X) (hK : IsCompact K) (hW : IsOpen W) (hKW : K ⊆ W)
    (hCover : ∀ x ∈ K, ∃ i, x ∈ (chart i).source)
    (Omega : ι → Set E)
    (hTarget : ∀ i, Omega i ⊆ (chart i).target)
    (hPhysical : ∀ i y, y ∈ Omega i → (chart i).symm y ∈ K)
    (T : ℕ → ℝ) (hT : ∀ k, 0 ≤ T k)
    (hTransition : ∀ (i j : ι) (k : ℕ), 1 ≤ k →
      ∀ y ∈ Omega i, y ∈ ((chart i).symm.trans (chart j)).source →
        ‖iteratedFDeriv ℝ k ((chart i).symm.trans (chart j)) y‖ ≤ T k)
    (f : X → F)
    (hf : ∀ i, ContDiffOn ℝ ∞ (f ∘ (chart i).symm)
      ((chart i).target ∩ (chart i).symm ⁻¹' W)) :
    ∃ C : ℕ → ℝ, (∀ k, 0 ≤ C k) ∧
      ∀ i k y, y ∈ Omega i → ‖iteratedFDeriv ℝ k (f ∘ (chart i).symm) y‖ ≤ C k := by
  classical
  obtain ⟨core,hCoreCompact,hCoreSub,hCoreCover⟩ :=
    original_finite_chart_compact_cores chart K W hK hW hKW hCover
  let V := fun i => (chart i).target ∩ (chart i).symm ⁻¹' W
  have hV : ∀ i, IsOpen (V i) := fun i =>
    (chart i).symm.continuousOn.isOpen_inter_preimage (chart i).open_target hW
  have hImageCompact : ∀ i, IsCompact ((chart i) '' core i) := fun i =>
    (hCoreCompact i).image_of_continuousOn ((chart i).continuousOn.mono
      (fun _ hx => (hCoreSub i hx).1))
  have hImageSub : ∀ i, (chart i) '' core i ⊆ V i := by
    intro i y hy
    obtain ⟨x,hx,rfl⟩ := hy
    refine ⟨(chart i).map_source (hCoreSub i hx).1,?_⟩
    change (chart i).symm (chart i x) ∈ W
    rw [(chart i).left_inv (hCoreSub i hx).1]
    exact (hCoreSub i hx).2
  have hPrefix : ∀ j : ℕ, ∃ R : ℝ, 0 ≤ R ∧ ∀ i k, k ≤ j →
      ∀ y ∈ (chart i) '' core i, ‖iteratedFDeriv ℝ k (f ∘ (chart i).symm) y‖ ≤ R := by
    intro j
    have hEach : ∀ a : ι × Fin (j+1), ∃ R : ℝ,
        ∀ y ∈ (chart a.1) '' core a.1,
          ‖iteratedFDeriv ℝ (a.2 : ℕ) (f ∘ (chart a.1).symm) y‖ ≤ R := by
      intro a
      obtain ⟨R,hR⟩ := parameterRound2_coordinate_jets_bounded_of_compact
        (f ∘ (chart a.1).symm) (V a.1) ((chart a.1) '' core a.1)
        ((chart a.1) '' core a.1) (hV a.1) (hImageCompact a.1)
        Subset.rfl (hImageSub a.1) (hf a.1) a.2
      exact ⟨R,fun y hy => hR ⟨⟨y,hy⟩,rfl⟩⟩
    choose R hR using hEach
    obtain ⟨B,hB⟩ := (Set.finite_range R).bddAbove
    refine ⟨max 0 B,le_max_left _ _,?_⟩
    intro i k hk y hy
    let a : ι × Fin (j+1) := (i,⟨k,by omega⟩)
    exact (hR a y hy).trans ((hB (mem_range_self a)).trans (le_max_right _ _))
  have hOrder : ∀ k : ℕ, ∃ C : ℝ, 0 ≤ C ∧
      ∀ i y, y ∈ Omega i → ‖iteratedFDeriv ℝ k (f ∘ (chart i).symm) y‖ ≤ C := by
    intro k
    obtain ⟨R,hR,hCore⟩ := hPrefix k
    refine ⟨(k.factorial : ℝ) * R * bufferedTransitionPrefix T k ^ k,
      mul_nonneg (mul_nonneg (Nat.cast_nonneg _) hR)
        (pow_nonneg ((by norm_num : (0:ℝ) ≤ 1).trans (one_le_bufferedTransitionPrefix hT k)) _),?_⟩
    intro i y hy
    let x := (chart i).symm y
    have hx : x ∈ ⋃ j, core j := by
      rw [← hCoreCover]
      exact hPhysical i y hy
    obtain ⟨j,hj⟩ := mem_iUnion.mp hx
    let e := (chart i).symm.trans (chart j)
    have he : y ∈ e.source := ⟨hTarget i hy,(hCoreSub j hj).1⟩
    have hyV : y ∈ V i := ⟨hTarget i hy,hKW (hPhysical i y hy)⟩
    let U := e.source ∩ V i
    have hU : IsOpen U := e.open_source.inter (hV i)
    have hSmooth : ContDiffOn ℝ ∞ e U := (hSmoothTransition i j).mono inter_subset_left
    have hMaps : MapsTo e U (V j) := by
      intro z hz
      refine ⟨(chart j).map_source hz.1.2,?_⟩
      change (chart j).symm (chart j ((chart i).symm z)) ∈ W
      have hzj : (chart i).symm z ∈ (chart j).source := hz.1.2
      rw [(chart j).left_inv hzj]
      exact hz.2.2
    have hEq : (f ∘ (chart i).symm) =ᶠ[𝓝 y] (f ∘ (chart j).symm) ∘ e := by
      filter_upwards [e.open_source.mem_nhds he] with z hz
      change f ((chart i).symm z) = f ((chart j).symm (chart j ((chart i).symm z)))
      have hzj : (chart i).symm z ∈ (chart j).source := hz.2
      rw [(chart j).left_inv hzj]
    rw [(hEq.iteratedFDeriv ℝ k).eq_of_nhds]
    apply parameter_general_composition_jet_le T hT hU (hV j)
      hSmooth (hf j) hMaps ⟨he,hyV⟩ k R
    · intro l hl
      exact hCore j l hl (e y) ⟨x,hj,rfl⟩
    · intro l hl _
      exact hTransition i j l hl y hy he
  choose C hC hBounds using hOrder
  exact ⟨C,hC,fun i k y hy => hBounds k i y hy⟩

end GlobalEmbedding.Continuation.FaithfulRepair

#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_finite_chart_compact_cores
#print axioms GlobalEmbedding.Continuation.FaithfulRepair.original_compact_observation_jet_profile_exists
