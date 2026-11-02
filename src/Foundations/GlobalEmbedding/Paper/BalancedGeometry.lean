import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Geometry.Manifold.MFDeriv.Basic
import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection

/-!
# Partial Gram matrix along smooth vector fields

Source: `literature/parallelizable-stable-plus-one/main.tex`, setup `setup:partial`, line 217.
For a smooth map into a Euclidean space and a finite family of smooth vector fields, the partial
Gram matrix is the Gram matrix of the target derivatives in those vector-field directions.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- The pointwise Gram matrix of the derivatives of `P` along the smooth vector fields `D`.

Its `(i,j)` entry is the Euclidean inner product of `dP(D i)` and `dP(D j)`. No linear
independence or positivity hypothesis is imposed. Source: `setup:partial`, line 217.
-/
noncomputable def balancedGeometry {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (_hP : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ P)
    (D : Fin a → ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (x : M) : Matrix (Fin a) (Fin a) ℝ :=
  Matrix.gram ℝ (fun i ↦
    tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (P x)
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) P x (D i x)))

end GlobalEmbedding.Paper
