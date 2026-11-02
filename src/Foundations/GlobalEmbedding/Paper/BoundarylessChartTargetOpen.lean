import GlobalEmbedding.Paper.GeneralChartRangeNeighborhood

open Filter Manifold Set
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- Every actual atlas chart on a boundaryless C² manifold has an open extended
target, even if the entire model with corners is not boundaryless.

Proof: every target point is the chart image of its inverse. Actual manifold
boundarylessness gives a neighborhood of this chart image inside the model range.
The chart target is already a relative neighborhood in that range, so it is an
ordinary neighborhood. Every point of the extended target is therefore interior.
Source: fixed coordinate domains in the smooth normal-form expansion of `defn:phase`. -/
theorem boundaryless_chart_target_open
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] (e : OpenPartialHomeomorph M H)
    (he : e ∈ atlas H M) : IsOpen (e.extend I).target := by
  apply isOpen_iff_mem_nhds.mpr
  intro z hz
  let x := (e.extend I).symm z
  have hx : x ∈ e.source := by
    simpa only [OpenPartialHomeomorph.extend_source] using (e.extend I).map_target hz
  have hr := general_chart_range_mem_nhds (I := I) e he x hx
  have ht := e.extend_target_mem_nhdsWithin (I := I) hx
  rw [nhdsWithin_eq_nhds.mpr hr] at ht
  simpa only [x, (e.extend I).right_inv hz] using ht

end GlobalEmbedding.Paper
