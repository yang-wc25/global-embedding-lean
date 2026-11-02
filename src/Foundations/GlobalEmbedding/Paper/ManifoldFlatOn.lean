import Mathlib.Geometry.Manifold.ContMDiff.Atlas
import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Geometry.Manifold.IsManifold.InteriorBoundary
import Mathlib.Analysis.Calculus.ContDiff.Basic

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- A smooth vector-valued function is flat on `Z` when every full coordinate
jet, including order zero, vanishes at every point of `Z` in every smooth chart.
The actual maximal smooth atlas is quantified, with the actual extended chart
inverse; ordinary jets are local because the source manifold has no boundary.
For empty `Z` this retains exactly smoothness, as in the source convention.
Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix`,
lines 285 and 299–323. -/
def ManifoldFlatOn
    {E H M F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : M → F) (Z : Set M) : Prop :=
  ContMDiff I 𝓘(ℝ, F) ∞ f ∧
    ∀ x ∈ Z, ∀ e : OpenPartialHomeomorph M H,
      e ∈ IsManifold.maximalAtlas I ∞ M → x ∈ e.source →
      ∀ k : ℕ, iteratedFDeriv ℝ k (f ∘ (e.extend I).symm) (e.extend I x) = 0

end GlobalEmbedding.Paper
