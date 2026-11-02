import GlobalEmbedding.Paper.NormalSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic

open Manifold

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`. -/

namespace GlobalEmbedding.Paper

/-- The normal projection annihilates each tangent vector in the image of the manifold
differential. Source: Definition `defn:phase`, lines 200–204. -/
theorem normal_projection_mfderiv_eq_zero
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M) (v : TangentSpace I x) :
    (normalSpace (I := I) f x).orthogonalProjectionOnto
      (tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (f x)
        (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) f x v)) = 0 := by
  apply Submodule.orthogonalProjectionOnto_eq_zero_iff.mpr
  apply Submodule.le_orthogonal_orthogonal
  exact ⟨v, rfl⟩

end GlobalEmbedding.Paper
