import GlobalEmbedding.Paper.FramedDistribution

/-!
# Full smooth tangent frames

Source: `literature/parallelizable-stable-plus-one/main.tex`, Section 7, Proposition
`prop:initialization`, proof lines 787–799. The proof uses a global tangent trivialization to
obtain a coframe. This module represents a full smooth frame as the already defined
`FramedDistribution` together with the condition that its pointwise span is the whole tangent
fiber.
-/

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- A full smooth tangent frame of length `n`, represented by a `FramedDistribution` whose
pointwise span is the entire tangent space. Source:
`literature/parallelizable-stable-plus-one/main.tex`, Section 7, Proposition
`prop:initialization`, proof lines 787–799. -/
structure FullTangentFrame (n : ℕ) where
  /-- The ordered smooth tangent fields and their pointwise independence. -/
  framed : FramedDistribution I (M := M) n
  /-- At each point, the frame vectors span the entire tangent space. -/
  spans : ∀ x : M, FramedDistribution.fiber I framed x = ⊤

end GlobalEmbedding.Paper
