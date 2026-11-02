import Mathlib.Geometry.Manifold.ContMDiff.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.FiniteDimension

open scoped ContDiff Manifold

namespace GlobalEmbedding.Paper

/-- A finite-domain operator field on an arbitrary charted manifold is smooth at
a point exactly when every actual vector evaluation is smooth there.

Proof: express both sides in the actual source chart using contMDiffAt_iff_source.
For normed targets the expressions are ordinary ContDiffWithinAt assertions.
Apply Mathlib's finite-domain operator evaluation criterion on the model range.
Source: finite local coefficient test for the true-form morphism in `defn:phase`. -/
theorem manifold_finite_operator_smooth_iff
    {X H M V W : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    [TopologicalSpace H] {I : ModelWithCorners ℝ X H}
    [TopologicalSpace M] [ChartedSpace H M]
    [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [NormedAddCommGroup W] [NormedSpace ℝ W]
    {n : ℕ∞ω} (A : M → V →L[ℝ] W) (x : M) :
    ContMDiffAt I 𝓘(ℝ, V →L[ℝ] W) n A x ↔
      ∀ v, ContMDiffAt I 𝓘(ℝ, W) n (fun y ↦ A y v) x := by
  simp only [contMDiffAt_iff_source, contMDiffWithinAt_iff_contDiffWithinAt,
    contDiffWithinAt_clm_apply, Function.comp_def]

end GlobalEmbedding.Paper
