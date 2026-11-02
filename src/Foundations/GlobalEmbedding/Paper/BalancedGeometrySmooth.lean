import GlobalEmbedding.Paper.BalancedDirectionalCalculus

/-!
# Smoothness of the original native partial Gram

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 374.
DAG node: `balanced-geometry-smooth`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The original native partial Gram of a smooth map along smooth fields is smooth.
Each actual directional derivative is smooth by the native tangent-map theorem. Compose
the smooth real inner product with their pair to obtain each genuine Gram entry, and use
coordinatewise finite-dimensional smoothness. This applies to any total space, including a
parameter product with its actual lifted smooth fields, without any compactness or frame
assumption. Source: smooth partial Gram in the hypotheses of `lem:balanced`. -/
theorem balancedGeometry_entry_contMDiff
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
    [TopologicalSpace M] [ChartedSpace H M] {I : ModelWithCorners ℝ E H}
    [IsManifold I ∞ M] {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :
    ∀ i j, ContMDiff I 𝓘(ℝ, ℝ) ∞ (fun x ↦ balancedGeometry P hP D x i j) := by
  intro i j
  have hi := balanced_directional_contMDiff P hP (D i)
  have hj := balanced_directional_contMDiff P hP (D j)
  exact (contDiff_inner (𝕜 := ℝ)).contMDiff.comp (hi.prodMk_space hj)

end GlobalEmbedding.Paper
