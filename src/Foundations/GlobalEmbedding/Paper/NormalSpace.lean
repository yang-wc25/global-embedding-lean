import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.InnerProductSpace.Orthogonal
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Geometry.Manifold.MFDeriv.Basic

/-!
# Normal spaces of maps into Euclidean space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`,
line 201. The normal space at a point is the Euclidean orthogonal complement of the range of
the total manifold derivative. It is defined for every map; for smooth immersions this is the
paper's normal space.
-/

noncomputable section

open Manifold

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The Euclidean orthogonal complement of the differential image at `x`.
Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`, line 201.
-/
def normalSpace {N : ℕ} (F : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    Submodule ℝ (EuclideanSpace ℝ (Fin N)) :=
  (LinearMap.range
    ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (F x)).toContinuousLinearMap.comp
      (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) F x)).toLinearMap).orthogonal

end GlobalEmbedding.Paper
