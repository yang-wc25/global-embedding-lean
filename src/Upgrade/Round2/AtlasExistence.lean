import GlobalEmbedding.Paper.BufferedAtlas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Data.Fintype.EquivFin
import Mathlib.Tactic.Linarith

/-!
# Actual finite smooth buffered atlases on a compact manifold

Source: the finite buffered atlas convention in `notation:averages` and
`setup:uniform` of the original paper.  The original `BufferedAtlas` is used
without modification.  We construct its data from the actual native charts,
first choosing concentric coordinate balls and then a finite subcover.  The
supports are inverse images of compact closed coordinate balls under the chart
inverse, not whole chart sources.

This is only the compact geometry needed to instantiate the upgrade chain.
No coloring, smoothing, probe family, incidence rank, or embedding is assumed.
-/

noncomputable section

open Set Metric Manifold GlobalEmbedding.Paper
open scoped ContDiff Topology

namespace GlobalEmbedding.Upgrade

section LocalChart

variable {M E : Type*} [TopologicalSpace M]
  [PseudoMetricSpace E] [ChartedSpace E M]

/-- A native chart contains a closed coordinate ball with a strict three-radius
buffer around the chart center.  All three radii refer to the same chart. -/
theorem exists_native_chart_closedBall_buffer (x : M) :
    ∃ r : ℝ, 0 < r ∧
      closedBall (chartAt E x x) (3 * r) ⊆ (chartAt E x).target := by
  obtain ⟨R, hR, hball⟩ :=
    Metric.isOpen_iff.mp (chartAt E x).open_target (chartAt E x x)
      ((chartAt E x).map_source (mem_chart_source E x))
  refine ⟨R / 4, by linarith, ?_⟩
  intro y hy
  apply hball
  rw [mem_ball]
  rw [mem_closedBall] at hy
  linarith

/-- The inner open coordinate ball of radius `r`, as an actual subset of `M`. -/
def nativeBufferedInner (x : M) (r : ℝ) : Set M :=
  (chartAt E x).source ∩ (chartAt E x) ⁻¹' ball (chartAt E x x) r

/-- The actual compact support in the same chart, with twice the inner radius. -/
def nativeBufferedSupport (x : M) (r : ℝ) : Set M :=
  (chartAt E x).symm '' closedBall (chartAt E x x) (2 * r)

theorem nativeBufferedInner_isOpen (x : M) (r : ℝ) :
    IsOpen (nativeBufferedInner (E := E) x r) :=
  (chartAt E x).isOpen_inter_preimage isOpen_ball

theorem mem_nativeBufferedInner (x : M) {r : ℝ} (hr : 0 < r) :
    x ∈ nativeBufferedInner (E := E) x r := by
  exact ⟨mem_chart_source E x, mem_ball_self hr⟩

theorem nativeBufferedSupport_subset_source (x : M) {r : ℝ} (hr : 0 < r)
    (hball : closedBall (chartAt E x x) (3 * r) ⊆ (chartAt E x).target) :
    nativeBufferedSupport (E := E) x r ⊆ (chartAt E x).source := by
  rintro y ⟨z, hz, rfl⟩
  apply (chartAt E x).map_target
  apply hball
  exact closedBall_subset_closedBall (by linarith) hz

theorem nativeBufferedSupport_isCompact [ProperSpace E] (x : M) {r : ℝ} (hr : 0 < r)
    (hball : closedBall (chartAt E x x) (3 * r) ⊆ (chartAt E x).target) :
    IsCompact (nativeBufferedSupport (E := E) x r) := by
  apply (isCompact_closedBall _ _).image_of_continuousOn
  apply (chartAt E x).continuousOn_symm.mono
  exact (closedBall_subset_closedBall (by linarith)).trans hball

theorem nativeBufferedInner_subset_interior_support (x : M) {r : ℝ} (hr : 0 < r) :
    nativeBufferedInner (E := E) x r ⊆
      interior (nativeBufferedSupport (E := E) x r) := by
  apply interior_maximal _ (nativeBufferedInner_isOpen x r)
  intro y hy
  refine ⟨chartAt E x y, ?_, (chartAt E x).left_inv hy.1⟩
  rw [mem_closedBall]
  have hdist := hy.2
  rw [mem_preimage, mem_ball] at hdist
  linarith

/-- The original positive buffer condition is proved for every point of the
inner domain.  A later finite minimum may only decrease the buffer. -/
theorem nativeBufferedInner_buffered (x : M) {r b : ℝ} (hr : 0 < r)
    (hball : closedBall (chartAt E x x) (3 * r) ⊆ (chartAt E x).target)
    (hb : b ≤ r) {y : M} (hy : y ∈ nativeBufferedInner (E := E) x r) :
    ball (chartAt E x y) b ⊆ (chartAt E x).target := by
  intro z hz
  apply hball
  rw [mem_closedBall]
  have hy' : dist (chartAt E x y) (chartAt E x x) < r := hy.2
  have hz' : dist z (chartAt E x y) < b := hz
  have htri := dist_triangle z (chartAt E x y) (chartAt E x x)
  linarith

end LocalChart

/-- A positive common lower bound for a finite family of positive radii.
The empty family uses radius `1`, so no nonemptiness assumption is needed. -/
theorem exists_positive_finite_radius {α : Type*} (s : Finset α)
    (r : α → ℝ) (hr : ∀ x, 0 < r x) :
    ∃ b : ℝ, 0 < b ∧ ∀ x ∈ s, b ≤ r x := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨1, zero_lt_one, by simp⟩
  | @insert x s hxs ih =>
      obtain ⟨b, hb, hbr⟩ := ih
      refine ⟨min (r x) b, lt_min (hr x) hb, ?_⟩
      intro y hy
      rcases Finset.mem_insert.mp hy with rfl | hy
      · exact min_le_left _ _
      · exact (min_le_right _ _).trans (hbr y hy)

variable {M E : Type*} [TopologicalSpace M]
  [NormedAddCommGroup E] [NormedSpace ℝ E] [ProperSpace E]
  [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- Every compact smooth manifold modeled on a proper normed real vector space
has an actual finite smooth buffered atlas with compact supports and an inner
cover lying in their interiors.  The charts are literal native charts of the
given manifold structure.  The construction works for an empty manifold, and
does not use connectedness, orientability, or a chosen immersion. -/
theorem exists_compact_smooth_bufferedAtlas [CompactSpace M] :
    ∃ A : BufferedAtlas M E,
      IsSmoothBufferedAtlas A ∧
      (∀ i, IsCompact (A.support i)) ∧
      (∀ i, A.inner i ⊆ interior (A.support i)) ∧
      (∀ x, ∃ i, x ∈ interior (A.support i)) ∧
      (∀ i, ∃ x : M, A.chart i = chartAt E x) := by
  classical
  choose r hr hball using exists_native_chart_closedBall_buffer (E := E) (M := M)
  let U : M → Set M := fun x ↦ nativeBufferedInner (E := E) x (r x)
  have hUopen : ∀ x, IsOpen (U x) := fun x ↦ nativeBufferedInner_isOpen x (r x)
  have hUcover : (univ : Set M) ⊆ ⋃ x, U x := by
    intro x _
    exact mem_iUnion.mpr ⟨x, mem_nativeBufferedInner x (hr x)⟩
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover U hUopen hUcover
  obtain ⟨b, hb, hbr⟩ := exists_positive_finite_radius s r hr
  let center : Fin s.card → M := fun i ↦ (s.equivFin.symm i).val
  have hcenter : ∀ i, center i ∈ s := fun i ↦ (s.equivFin.symm i).property
  have hcover : ∀ x, ∃ i : Fin s.card, x ∈ U (center i) := by
    intro x
    obtain ⟨y, hys, hxy⟩ := mem_iUnion₂.mp (hs (mem_univ x))
    refine ⟨s.equivFin ⟨y, hys⟩, ?_⟩
    simpa only [center, Equiv.symm_apply_apply] using hxy
  let A : BufferedAtlas M E := {
    count := s.card
    chart := fun i ↦ chartAt E (center i)
    inner := fun i ↦ U (center i)
    inner_open := fun i ↦ hUopen (center i)
    inner_subset := fun _ ↦ inter_subset_left
    cover := hcover
    buffer := b
    buffer_pos := hb
    buffered := fun i _ hy ↦ nativeBufferedInner_buffered (center i)
      (hr (center i)) (hball (center i)) (hbr _ (hcenter i)) hy
    support := fun i ↦ nativeBufferedSupport (E := E) (center i) (r (center i)) }
  have hinner : ∀ i, A.inner i ⊆ interior (A.support i) := fun i ↦
    nativeBufferedInner_subset_interior_support (center i) (hr (center i))
  refine ⟨A, ⟨?_, ?_⟩, ?_, hinner, ?_, ?_⟩
  · intro i
    exact IsManifold.chart_mem_maximalAtlas (center i)
  · intro i
    exact nativeBufferedSupport_subset_source (center i) (hr _) (hball _)
  · intro i
    exact nativeBufferedSupport_isCompact (center i) (hr _) (hball _)
  · intro x
    obtain ⟨i, hi⟩ := A.cover x
    exact ⟨i, hinner i hi⟩
  · intro i
    exact ⟨center i, rfl⟩

end GlobalEmbedding.Upgrade
