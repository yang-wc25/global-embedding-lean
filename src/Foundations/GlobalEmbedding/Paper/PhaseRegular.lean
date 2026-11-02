import GlobalEmbedding.Paper.GoodCovector

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The source phase condition: every point has an actual good covector.
For a smooth immersion this is precisely phase regularity in `defn:phase`.
The property extends to other smooth maps; immersion remains a separate required
condition whenever the source or a target says "phase-regular immersion".
No auxiliary metric or selected covector field is part of this predicate. -/
def PhaseRegular
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) : Prop :=
  ∀ x : M, ∃ ξ : TangentSpace I x →L[ℝ] ℝ, GoodCovector f hf x ξ

end GlobalEmbedding.Paper
