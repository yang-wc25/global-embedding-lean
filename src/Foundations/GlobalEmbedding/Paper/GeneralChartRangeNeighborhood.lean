import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, chart-independence of the normal second form. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- Every actual atlas chart on a boundaryless C² manifold places the point in the
interior of the model range.
Proof: interior points are invariant under atlas transitions; boundarylessness makes
x interior in its centered chart, hence also in the selected chart.
Source: `defn:phase`, chart-independence of the normal second form. -/
theorem general_chart_range_mem_nhds
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 2 M]
    [BoundarylessManifold I M] (e : OpenPartialHomeomorph M H)
    (he : e ∈ atlas H M) (x : M) (hx : x ∈ e.source) :
    Set.range I ∈ 𝓝 (e.extend I x) := by
  have hi : e.extend I x ∈ interior (e.extend I).target :=
    (ModelWithCorners.isInteriorPoint_iff_of_mem_atlas (I := I) (n := 2)
      (by norm_num) he hx).mp (BoundarylessManifold.isInteriorPoint (x := x))
  exact mem_interior_iff_mem_nhds.mp
    (OpenPartialHomeomorph.interior_extend_target_subset_interior_range e hi)

end GlobalEmbedding.Paper
