import GlobalEmbedding.Paper.LeastSingularNorm
import GlobalEmbedding.Paper.SymmetricSquareMapL
import Mathlib.Analysis.Normed.Module.FiniteDimension

open scoped TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance restrictionSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance restrictionSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The literal restriction of an actual symmetric-square operator to the actual
kernel of a covector, with the canonical induced quotient norm.
Source: `defn:phase`, restriction of the true second form. -/
noncomputable def covectorRestriction
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (S : SymmetricSquare E →L[ℝ] F) (ξ : E →L[ℝ] ℝ) :
    SymmetricSquare ξ.ker →L[ℝ] F :=
  S.comp (symmetricSquareMapL ξ.ker.subtypeL)

end GlobalEmbedding.Paper
