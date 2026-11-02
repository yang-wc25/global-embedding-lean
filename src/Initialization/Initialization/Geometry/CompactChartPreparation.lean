import GlobalEmbedding.Paper.BufferedAtlas
import Mathlib.Topology.MetricSpace.ProperSpace
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Lemmas
import Mathlib.Data.Finset.Max
import Mathlib.Tactic

/-!
# Genuine compact chart preparation

Finite smooth charts, compact coordinate buffers and a common ambient support
radius are constructed from compactness of the original manifold. This is an
alternate to the still-unproved exponential-chart route in the historical DAG.
It changes no target statement and assumes no uniform geometry as input.
-/

open Set Metric Manifold IsManifold Topology
open scoped ContDiff Manifold

noncomputable section
namespace GlobalEmbedding.Initialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {M : Type*} [TopologicalSpace M] [ChartedSpace E M]

/-- Compactness of the source produces finitely many actual maximal-atlas
charts with a closed four-radius coordinate buffer. Their smaller coordinate
balls cover M. Empty sources and the zero-dimensional model are retained. -/
theorem exists_finite_compact_chart_cover [IsManifold 𝓘(ℝ, E) ∞ M]
    [CompactSpace M] :
    ∃ (m : ℕ) (e : Fin m → OpenPartialHomeomorph M E)
      (a : Fin m → E) (r : Fin m → ℝ),
      (∀ i, e i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) ∧ (∀ i, 0 < r i) ∧
      (∀ i, closedBall (a i) (4 * r i) ⊆ (e i).target) ∧
      ∀ x : M, ∃ i, x ∈ (e i).source ∧ e i x ∈ ball (a i) (r i) := by
  have localRadius (p : M) : ∃ r : ℝ, 0 < r ∧
      closedBall (chartAt E p p) (4 * r) ⊆ (chartAt E p).target := by
    obtain ⟨R, hR, hsub⟩ := Metric.isOpen_iff.mp (chartAt E p).open_target
      (chartAt E p p) ((chartAt E p).map_source (mem_chart_source E p))
    refine ⟨R / 8, by positivity, ?_⟩
    exact (closedBall_subset_ball (by linarith : 4 * (R / 8) < R)).trans hsub
  choose r hr hbuffer using localRadius
  let U : M → Set M := fun p ↦
    (chartAt E p).source ∩ (chartAt E p) ⁻¹' ball (chartAt E p p) (r p)
  have hU (p : M) : IsOpen (U p) := (chartAt E p).isOpen_inter_preimage isOpen_ball
  have hpU (p : M) : p ∈ U p := ⟨mem_chart_source E p, by simpa using hr p⟩
  obtain ⟨t, ht⟩ := (isCompact_univ : IsCompact (univ : Set M)).elim_finite_subcover
    U hU (by intro p _; exact mem_iUnion.mpr ⟨p, hpU p⟩)
  let J := {p : M // p ∈ t}
  let toJ := (Fintype.equivFin J).symm
  let p : Fin (Fintype.card J) → M := fun i ↦ (toJ i).val
  refine ⟨Fintype.card J, (fun i ↦ chartAt E (p i)),
    (fun i ↦ chartAt E (p i) (p i)), (fun i ↦ r (p i)),
    (fun i ↦ chart_mem_maximalAtlas (p i)), (fun i ↦ hr (p i)),
    (fun i ↦ hbuffer (p i)), ?_⟩
  intro x
  obtain ⟨q, hqt, hxq⟩ := mem_iUnion₂.mp (ht (mem_univ x))
  refine ⟨Fintype.equivFin J ⟨q, hqt⟩, ?_⟩
  simpa only [p, toJ, Equiv.symm_apply_apply, U, Set.mem_inter_iff, Set.mem_preimage] using hxq

/-- A native smooth buffered atlas with compact enlarged supports exists from
the manifold assumptions alone. The original `BufferedAtlas` definition is used.
This fixed atlas is preparation for the scale-dependent refinement, not a claim
that the refinement or its transition estimates have already been constructed. -/
theorem exists_compact_smooth_buffered_atlas
    [FiniteDimensional ℝ E] [IsManifold 𝓘(ℝ, E) ∞ M]
    [T2Space M] [CompactSpace M] :
    ∃ A : GlobalEmbedding.Paper.BufferedAtlas M E,
      GlobalEmbedding.Paper.IsSmoothBufferedAtlas A ∧
      (∀ i, IsCompact (A.support i)) ∧ (∀ i, A.inner i ⊆ A.support i) := by
  obtain ⟨m, e, a, r, he, hr, hbuffer, hcover⟩ :=
    exists_finite_compact_chart_cover (E := E) (M := M)
  let radii : Finset ℝ := insert 1 (Finset.univ.image r)
  have hrad : radii.Nonempty := by simp [radii]
  let b : ℝ := radii.min' hrad
  have hb : 0 < b := by
    have hmem : b ∈ radii := Finset.min'_mem radii hrad
    rcases Finset.mem_insert.mp hmem with h | h
    · simpa only [h] using (zero_lt_one : (0 : ℝ) < 1)
    · obtain ⟨i, _, hi⟩ := Finset.mem_image.mp h
      exact hi ▸ hr i
  have hbr (i : Fin m) : b ≤ r i :=
    Finset.min'_le radii (r i) (Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩))
  let A : GlobalEmbedding.Paper.BufferedAtlas M E :=
    { count := m
      chart := e
      inner := fun i ↦ (e i).source ∩ e i ⁻¹' ball (a i) (r i)
      inner_open := fun i ↦ (e i).isOpen_inter_preimage isOpen_ball
      inner_subset := fun _ _ hx ↦ hx.1
      cover := hcover
      buffer := b
      buffer_pos := hb
      buffered := by
        intro i x hx y hy
        apply hbuffer i
        rw [Metric.mem_closedBall]
        have h1 : dist y (e i x) < b := hy
        have h2 : dist (e i x) (a i) < r i := hx.2
        have h3 := dist_triangle y (e i x) (a i)
        linarith [hbr i, hr i]
      support := fun i ↦ (e i).symm '' closedBall (a i) (2 * r i) }
  have htwo (i : Fin m) : closedBall (a i) (2 * r i) ⊆ (e i).target :=
    (closedBall_subset_closedBall (by linarith [hr i])).trans (hbuffer i)
  refine ⟨A, ⟨he, ?_⟩, ?_, ?_⟩
  · intro i x hx
    obtain ⟨y, hy, rfl⟩ := hx
    exact (e i).map_target (htwo i hy)
  · intro i
    exact (isCompact_closedBall _ _).image_of_continuousOn
      ((e i).continuousOn_symm.mono (htwo i))
  · intro i x hx
    refine ⟨e i x, ?_, (e i).left_inv hx.1⟩
    exact (closedBall_subset_closedBall (by linarith [hr i]))
      (ball_subset_closedBall hx.2)

/-- A genuine embedding of a compact source supplies a common positive radius
whose ambient closed-ball pullbacks are subordinate to an arbitrary open cover.
The induced metric retains exactly the original topology. -/
theorem exists_uniform_ambient_closedBall_subordinate
    {F : Type*} [MetricSpace F] [CompactSpace M]
    (e : M → F) (he : IsEmbedding e) {κ : Type*}
    (U : κ → Set M) (hU : ∀ i, IsOpen (U i)) (hcover : ∀ x, ∃ i, x ∈ U i) :
    ∃ ρ : ℝ, 0 < ρ ∧ ∀ p : M, ∃ i,
      e ⁻¹' closedBall (e p) ρ ⊆ U i := by
  letI : MetricSpace M := he.comapMetricSpace e
  obtain ⟨δ, hδ, hlocal⟩ := lebesgue_number_lemma_of_metric
    (isCompact_univ : IsCompact (univ : Set M)) hU
    (by intro x _; exact mem_iUnion.mpr (hcover x))
  refine ⟨δ / 2, by positivity, ?_⟩
  intro p
  obtain ⟨i, hi⟩ := hlocal p (mem_univ p)
  refine ⟨i, ?_⟩
  intro x hx
  apply hi
  change dist (e x) (e p) < δ
  change dist (e x) (e p) ≤ δ / 2 at hx
  exact hx.trans_lt (half_lt_self hδ)

end GlobalEmbedding.Initialization
