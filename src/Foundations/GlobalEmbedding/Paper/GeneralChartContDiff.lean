import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace

/-!
# Smoothness in a general extended chart at an interior point

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`.
The coordinate representative is defined on the ambient model vector space. Actual
boundarylessness makes the range of the model a neighborhood of the base point.
-/

open Manifold
open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- A Cⁿ Euclidean-valued map on a boundaryless manifold is Cⁿ in the centered
extended chart, for arbitrary model with corners.

Proof: the definition of ContMDiffAt gives Cⁿ within the model range. Every point of a
boundaryless manifold is interior, so that range is a neighborhood at the coordinate
center. Restriction to a neighborhood imposes no loss of differentiability.
Source: Definition `defn:phase`, local coordinate construction of the second form. -/
theorem contDiffAt_general_chart_representative
    {E F H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M]
    {n : ℕ∞ω} {f : M → F} {x : M}
    (hf : ContMDiffAt I 𝓘(ℝ, F) n f x) :
    ContDiffAt ℝ n (f ∘ (extChartAt I x).symm) (extChartAt I x x) := by
  have hc := (contMDiffAt_iff.mp hf).2
  have hr : Set.range I ∈ 𝓝 (extChartAt I x x) :=
    range_mem_nhds_isInteriorPoint (BoundarylessManifold.isInteriorPoint (x := x))
  simpa only [mfld_simps] using hc.contDiffAt hr

end GlobalEmbedding.Paper
