import Initialization.Geometry.CoframeFreezing
import Mathlib.Geometry.Manifold.PartitionOfUnity
import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Topology.Algebra.Support

/-!
# Actual global extensions of fixed coordinate maps

A fixed compact chart core admits a global smooth coordinate extension equal
to the same original chart on that core. It is obtained from native smooth
separation and multiplication, not postulated. These extensions allow bounded
coordinate comparisons along convex parent-chart segments even when those
segments leave a different chart's source.
-/

open Set Filter Manifold IsManifold Topology
open scoped ContDiff Manifold Topology

noncomputable section
namespace GlobalEmbedding.Initialization

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace M] [ChartedSpace E M]
  [IsManifold 𝓘(ℝ, E) ∞ M] [T2Space M] [CompactSpace M]

/-- A compact subset of a genuine chart source supplies a smooth scalar cutoff
which is one near that subset and whose topological support lies in the same
source. This handles the zero-extension boundary without assuming it away. -/
theorem exists_smooth_chart_core_cutoff
    (e : OpenPartialHomeomorph M E) {K : Set M}
    (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ f : M → ℝ, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ f ∧
      (∀ x ∈ K, f x = 1) ∧ tsupport f ⊆ e.source := by
  have hd : Disjoint e.sourceᶜ K := by
    apply Set.disjoint_left.mpr
    intro x hx hxK
    exact hx (hKe hxK)
  obtain ⟨f, hzero, hone, _hrange⟩ :=
    exists_contMDiffMap_zero_one_nhds_of_isClosed (𝓘(ℝ, E))
      e.open_source.isClosed_compl hK.isClosed hd (n := (⊤ : ℕ∞))
  refine ⟨f, f.contMDiff, fun x hx ↦ hone.self_of_nhdsSet x hx, ?_⟩
  intro x hx
  by_contra hxe
  have hz : (f : M → ℝ) =ᶠ[𝓝 x] (0 : M → ℝ) :=
    (nhds_le_nhdsSet hxe) hzero
  exact (notMem_tsupport_iff_eventuallyEq.mpr hz) hx

/-- A true global smooth map agreeing with the original chart on the given
compact core. The smoothness proof uses the actual topological support and the
original maximal-atlas membership. -/
theorem exists_smooth_coordinate_extension
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {K : Set M} (hK : IsCompact K) (hKe : K ⊆ e.source) :
    ∃ f : M → E, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f ∧ EqOn f e K := by
  obtain ⟨χ, hχ, hone, hsupp⟩ := exists_smooth_chart_core_cutoff e hK hKe
  let f : M → E := fun x ↦ χ x • e x
  refine ⟨f, ?_, ?_⟩
  · apply contMDiff_of_tsupport
    intro x hx
    have hxe : x ∈ e.source := hsupp (tsupport_smul_subset_left _ _ hx)
    exact hχ.contMDiffAt.smul (contMDiffAt_of_mem_maximalAtlas he hxe)
  · intro x hx
    change χ x • e x = e x
    rw [hone x hx, one_smul]

/-- The genuine chart pullback of a smooth global coordinate extension has
uniform all-order bounds on every compact coordinate core. The constants are
obtained internally from continuity of the actual derivatives. -/
theorem exists_coordinate_extension_pullback_bounds
    (f : M → E) (hf : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, E) ∞ f)
    (e : OpenPartialHomeomorph M E)
    (he : e ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    {s : Set E} (hs : IsCompact s) (hse : s ⊆ e.target) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ j y, y ∈ s → ‖iteratedFDeriv ℝ j (f ∘ e.symm) y‖ ≤ B j := by
  have hcoord : ContDiffOn ℝ ∞ (f ∘ e.symm) e.target :=
    (hf.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas he)).contDiffOn
  exact exists_compact_smooth_derivative_bounds hs e.open_target hse _ hcoord

end GlobalEmbedding.Initialization
