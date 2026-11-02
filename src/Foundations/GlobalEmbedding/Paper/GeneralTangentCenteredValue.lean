import GlobalEmbedding.Paper.GeneralTangentTrivialization

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- At the coordinate center the actual trivialization represents the model tangent vector.
Source: `defn:phase`, pointwise covariant-Hessian comparison. -/
theorem tangent_section_general_centered_value
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
    (V : ∀ z : M, TangentSpace I z) (x : M) :
    (trivializationAt E (TangentSpace I) x
      ⟨(extChartAt I x).symm (extChartAt I x x),
        V ((extChartAt I x).symm (extChartAt I x x))⟩).2 =
      tangentSpaceCastModel I x (V x) := by
  rw [extChartAt_to_inv,
    tangent_section_general_trivialization_eq_chart_derivative V x x (mem_chart_source H x)]
  rw [mfderiv_extChartAt_self]
  rfl

end GlobalEmbedding.Paper
