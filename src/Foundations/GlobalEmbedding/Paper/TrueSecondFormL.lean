import GlobalEmbedding.Paper.TrueSecondForm
import GlobalEmbedding.Paper.SymmetricSquareNorms
import Mathlib.Topology.Algebra.Module.FiniteDimension
import Mathlib.Topology.VectorBundle.Riemannian

open Bundle Manifold
open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance trueLSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance trueLSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual entire true second form as a continuous linear map with canonical
Hilbert quotient norm on its source and the induced Euclidean normal-space norm.
Finite dimension supplies continuity of the existing linear map.
Source: `defn:phase`, true second form as a symmetric-square operator. -/
noncomputable def trueSecondFormL
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M) :
    SymmetricSquare (TangentSpace I x) →L[ℝ] normalSpace (I := I) f x :=
  LinearMap.toContinuousLinearMap (trueSecondForm f hf x)

end GlobalEmbedding.Paper
