import GlobalEmbedding.Paper.GeneralMaximalChartRangeNeighborhood

open Filter Manifold Set
open scoped ContDiff Topology

namespace GlobalEmbedding.Paper

/-- An actual maximal smooth chart on a boundaryless manifold has open extended
target, even beyond the chosen atlas. Proof: at each target point the general
maximal-chart interior theorem turns its relative target neighborhood into an
ordinary neighborhood. Source: `prop:matrix`, all local coordinate jets. -/
theorem general_maximal_chart_target_open
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] (e : OpenPartialHomeomorph M H)
    (he : e ∈ IsManifold.maximalAtlas I 2 M) : IsOpen (e.extend I).target := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  let x := (e.extend I).symm z
  have hx : x ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hz
  have hr := general_maximal_chart_range_mem_nhds e he x hx
  have ht := e.extend_target_mem_nhdsWithin (I := I) hx
  rw [nhdsWithin_eq_nhds.mpr hr] at ht
  simpa only [x, (e.extend I).right_inv hz] using ht

end GlobalEmbedding.Paper
