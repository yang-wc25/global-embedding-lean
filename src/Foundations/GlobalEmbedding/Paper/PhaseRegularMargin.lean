import GlobalEmbedding.Paper.PhaseRegular
import GlobalEmbedding.Paper.TruePhaseMarginPositiveGoodCovector

open Bundle Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual pointwise positive phase margin is exactly the norm-independent
phase condition in tangent dimension at least two.
Proof: apply the actual positive-margin/good-covector equivalence at each point.
No uniform lower bound or continuous choice is inferred. Source: `defn:phase`. -/
theorem phase_regular_iff_positive_true_margin
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}
    (hdim : 2 ≤ Module.finrank ℝ E) (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) :
    PhaseRegular f hf ↔ ∀ x : M, 0 < truePhaseMargin f hf x := by
  constructor
  · intro h x
    exact (true_phase_margin_positive_iff_good_covector hdim f hf x).mpr (h x)
  · intro h x
    exact (true_phase_margin_positive_iff_good_covector hdim f hf x).mp (h x)

end GlobalEmbedding.Paper
