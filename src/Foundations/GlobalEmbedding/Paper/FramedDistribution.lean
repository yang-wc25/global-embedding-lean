import Mathlib.Geometry.Manifold.VectorBundle.Tangent
import Mathlib.Geometry.Manifold.VectorBundle.ContMDiffSection
import Mathlib.LinearAlgebra.LinearIndependent.Defs

/-!
# Framed tangent distributions

Source: `literature/parallelizable-stable-plus-one/main.tex`, Lemma `lem:planar`.
A framed distribution is specified by its ordered smooth frame; its fiber at a point is the
linear span of the frame vectors there.
-/

open scoped Manifold ContDiff

namespace GlobalEmbedding.Paper

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  {H : Type*} [TopologicalSpace H] (I : ModelWithCorners ℝ E H)
  {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]

/-- An ordered frame of `b` smooth tangent vector fields, pointwise linearly independent.
Its pointwise span is the framed rank-`b` distribution in Lemma `lem:planar`.
This imposes no global frame on the rest of the tangent bundle and permits `b = 0`. -/
structure FramedDistribution (b : ℕ) where
  /-- The ordered smooth tangent fields forming the frame. -/
  frame : Fin b → ContMDiffSection I E ∞ (TangentSpace I : M → Type _)
  /-- The frame vectors are linearly independent in every tangent space. -/
  independent : ∀ x : M, LinearIndependent ℝ (fun i ↦ frame i x)

/-- The tangent subspace spanned by the frame at `x`, as in Lemma `lem:planar`. -/
noncomputable def FramedDistribution.fiber {b : ℕ} (D : FramedDistribution I (M := M) b) (x : M) :
    Submodule ℝ (TangentSpace I x) :=
  Submodule.span ℝ (Set.range fun i ↦ D.frame i x)

end GlobalEmbedding.Paper
