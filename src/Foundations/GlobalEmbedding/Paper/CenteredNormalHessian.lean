import GlobalEmbedding.Paper.NormalSpace
import Mathlib.Analysis.InnerProductSpace.Projection.Basic
import Mathlib.LinearAlgebra.BilinearMap

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter Manifold Set
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- The centered coordinate Hessian, as an actual normal-valued real bilinear map.
Its data are the full derivative, canonical tangent casts and orthogonal projection.
Source: `defn:phase`, normal-valued bilinear form underlying the symmetric-square map. -/
noncomputable def centeredNormalHessian
    {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N)) (x : M) :
    TangentSpace I x →ₗ[ℝ] TangentSpace I x →ₗ[ℝ] normalSpace (I := I) f x :=
  LinearMap.mk₂ ℝ (fun v w ↦ (normalSpace (I := I) f x).orthogonalProjectionOnto
      (fderiv ℝ (fderiv ℝ (f ∘ (extChartAt I x).symm)) (extChartAt I x x)
        (tangentSpaceCastModel I x v) (tangentSpaceCastModel I x w)))
    (by intro v v' w; simp only [map_add, add_apply])
    (by intro r v w; simp only [map_smul, smul_apply])
    (by intro v w w'; simp only [map_add])
    (by intro r v w; simp only [map_smul])

end GlobalEmbedding.Paper
