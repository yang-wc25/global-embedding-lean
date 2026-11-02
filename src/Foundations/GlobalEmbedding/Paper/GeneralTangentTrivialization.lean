import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.MFDeriv.Atlas

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- The actual tangent trivialization is the differential of the extended chart.
Source: `defn:phase`, coordinate expression of dF applied to a tangent field. -/
theorem tangent_section_general_trivialization_eq_chart_derivative
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (V : ∀ z : M, TangentSpace I z) (x p : M) (hp : p ∈ (chartAt H x).source) :
    (trivializationAt E (TangentSpace I) x ⟨p, V p⟩).2 =
      tangentSpaceCastModel 𝓘(ℝ, E) (extChartAt I x p)
        (mfderiv I 𝓘(ℝ, E) (extChartAt I x) p (V p)) := by
  rw [← (trivializationAt E (TangentSpace I) x).continuousLinearMapAt_apply_of_mem ℝ hp]
  rw [TangentBundle.continuousLinearMapAt_trivializationAt (I := I) hp]
  rfl

end GlobalEmbedding.Paper
