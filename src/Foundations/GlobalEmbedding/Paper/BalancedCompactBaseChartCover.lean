import Mathlib.Geometry.Manifold.ChartedSpace
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Topology.MetricSpace.ProperSpace

/-!
# Actual compact base-chart cover subordinate to the original local bundle domains

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines403–418.
DAG node: `balanced-compact-base-chart-cover`.
-/

open Set

namespace GlobalEmbedding.Paper

/-- A compact native manifold has a finite chart cover with actual compact coordinate
balls inside the original local domains.

Proof: choose an original covering domain at each base point. In its native chart,
the intersection of the chart target and the inverse image of that domain is open
and contains the coordinate center. Choose a ball there and halve its radius, so the
closed smaller ball is still inside. Finite-dimensional coordinate space makes that
closed ball compact. The inverse images of the open smaller balls cover the original
base; actual compactness selects finitely many. This uses no separation assumption,
global chart, frame, connectedness or nonemptiness. The empty base has an empty finite
cover, and zero-dimensional coordinate models retain positive radii.
Source: compact base and local trivializations in the proof of `lem:balanced`. -/
theorem balanced_compact_base_chart_cover
    {E B ι : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace B] [ChartedSpace E B] [CompactSpace B]
    (U : ι → Set B) (hU : ∀ i, IsOpen (U i))
    (hcover : ∀ b : B, ∃ i : ι, b ∈ U i) :
    ∃ centers : Finset B, ∃ index : B → ι, ∃ radius : B → ℝ,
      (∀ b : B, 0 < radius b ∧
        IsOpen ((chartAt E b).target ∩ (chartAt E b).symm ⁻¹' U (index b)) ∧
        IsCompact (Metric.closedBall (chartAt E b b) (radius b)) ∧
        Metric.closedBall (chartAt E b b) (radius b) ⊆
          (chartAt E b).target ∩ (chartAt E b).symm ⁻¹' U (index b)) ∧
      ∀ x : B, ∃ b ∈ centers, x ∈ (chartAt E b).source ∧
        chartAt E b x ∈ Metric.ball (chartAt E b b) (radius b) := by
  classical
  choose index hindex using hcover
  have hopen (b : B) :
      IsOpen ((chartAt E b).target ∩ (chartAt E b).symm ⁻¹' U (index b)) :=
    (chartAt E b).isOpen_inter_preimage_symm (hU (index b))
  have hcenter (b : B) : chartAt E b b ∈
      (chartAt E b).target ∩ (chartAt E b).symm ⁻¹' U (index b) := by
    refine ⟨mem_chart_target E b, ?_⟩
    change (chartAt E b).symm (chartAt E b b) ∈ U (index b)
    rw [(chartAt E b).left_inv (mem_chart_source E b)]
    exact hindex b
  have hballs (b : B) : ∃ r : ℝ, 0 < r ∧
      Metric.closedBall (chartAt E b b) r ⊆
        (chartAt E b).target ∩ (chartAt E b).symm ⁻¹' U (index b) := by
    obtain ⟨r, hr, hsub⟩ := Metric.isOpen_iff.mp (hopen b) _ (hcenter b)
    exact ⟨r / 2, by positivity,
      (Metric.closedBall_subset_ball (by linarith : r / 2 < r)).trans hsub⟩
  choose radius hpositive hsubset using hballs
  let inner (b : B) : Set B := (chartAt E b).source ∩
    (chartAt E b) ⁻¹' Metric.ball (chartAt E b b) (radius b)
  have hinner (b : B) : IsOpen (inner b) :=
    (chartAt E b).isOpen_inter_preimage Metric.isOpen_ball
  have hself (b : B) : b ∈ inner b :=
    ⟨mem_chart_source E b, Metric.mem_ball_self (hpositive b)⟩
  obtain ⟨centers, hcenters⟩ := isCompact_univ.elim_finite_subcover inner hinner
    (show (univ : Set B) ⊆ ⋃ b, inner b by
      intro b _
      exact mem_iUnion.mpr ⟨b, hself b⟩)
  refine ⟨centers, index, radius, ?_, ?_⟩
  · intro b
    exact ⟨hpositive b, hopen b, isCompact_closedBall _ _, hsubset b⟩
  · intro x
    obtain ⟨b, hb, hx⟩ := mem_iUnion₂.mp (hcenters (mem_univ x))
    exact ⟨b, hb, hx⟩

#print axioms balanced_compact_base_chart_cover

end GlobalEmbedding.Paper
