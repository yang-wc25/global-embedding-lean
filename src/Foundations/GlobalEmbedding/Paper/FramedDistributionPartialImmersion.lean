import GlobalEmbedding.Paper.FramedDistributionSmoothCoframe
import GlobalEmbedding.Paper.FramedPartialImmersionFormal

/-!
# Framed distributions admit partial immersions in one higher target dimension

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:planar`, first assertion.
This module consumes the genuine global coframe existence theorem; no coframe, metric,
formal solution, openness or ampleness is added as a hypothesis.
-/

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

/-- A framed rank-b distribution on a closed manifold has an actual smooth partial immersion
into R^(b+1). Empty manifolds, disconnected sources, and b=0 are included.

Proof: construct the genuine global smooth dual coframe. Compose it with the injective
coordinate inclusion R^b→R^(b+1), giving an explicit zero-valued smooth formal jet. Its frame
images are independent, hence it lies in the actual framed partial-immersion relation. That
relation is open by smooth jet-field evaluation, and ample by the actual codimension-two
principal-slice calculation. The proved global maps h-principle has a holonomic endpoint;
its underlying smooth map has the required derivative restriction. -/
theorem framed_distribution_partial_immersion_exists
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    [TopologicalSpace H] (I : ModelWithCorners ℝ E H) [I.Boundaryless]
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [T2Space M] [SecondCountableTopology M] [CompactSpace M]
    {b : ℕ} (V : FramedDistribution I (M := M) b) :
    ∃ f : M → EuclideanSpace ℝ (Fin (b + 1)),
      ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin (b + 1))) ∞ f ∧
      ∀ x : M, Function.Injective
        (fun v : FramedDistribution.fiber I V x ↦
          mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin (b + 1))) f x v.1) := by
  obtain ⟨B, hB⟩ := framed_distribution_smooth_coframe I V
  exact framedPartial_exists_of_smoothCoframe V B hB

end GlobalEmbedding.Paper
