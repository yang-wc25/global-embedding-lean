import GlobalEmbedding.Paper.NormalProjectionTangent
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Geometry.Manifold.MFDeriv.NormedSpace

/-!
# Normal projection kills the derivative in a general extended chart

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`.
Unlike the recovered self-model helper, this allows any model with corners and uses
boundarylessness of the actual manifold to obtain a genuine open neighborhood at x.
-/

open Manifold
open scoped Topology

namespace GlobalEmbedding.Paper

/-- On a boundaryless manifold the normal projection kills the full derivative of the
Euclidean coordinate representative in the centered extended chart.

Proof: the manifold derivative uses a derivative within `range I`. At an interior point,
that range is a neighborhood of the coordinate center, so the within derivative equals
the full derivative. The tangent-image projection lemma annihilates its image.
Source: Definition `defn:phase`, chart-independence of the true second form. -/
theorem normal_projection_general_chart_derivative
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M)
    (hf : MDifferentiableAt I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x) (v : E) :
    (normalSpace (I := I) f x).orthogonalProjectionOnto
      (fderiv ℝ (f ∘ (extChartAt I x).symm) (extChartAt I x x) v) = 0 := by
  have hp := normal_projection_mfderiv_eq_zero (I := I) f x
    ((tangentSpaceCastModel I x).symm v)
  have hr : Set.range I ∈ 𝓝 (extChartAt I x x) :=
    range_mem_nhds_isInteriorPoint (BoundarylessManifold.isInteriorPoint (x := x))
  rw [← fderivWithin_of_mem_nhds (𝕜 := ℝ) (f := f ∘ (extChartAt I x).symm) hr]
  simpa [mfderiv, hf, writtenInExtChartAt, modelWithCornersSelf_coe] using hp

end GlobalEmbedding.Paper
