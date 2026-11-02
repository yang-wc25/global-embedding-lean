import GlobalEmbedding.Paper.CovectorRestriction

open scoped TensorProduct

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance bestSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance bestSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The actual supremum over unit covectors of the actual restricted minimum
singular norm. Identification with the source maximum requires the separate
maximum-attainment theorem, and is not assumed in this data definition.
Source: `defn:phase`, best-phase margin. -/
noncomputable def bestPhaseSupremum
    {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] (S : SymmetricSquare E →L[ℝ] F) : ℝ :=
  sSup ((fun ξ : E →L[ℝ] ℝ ↦ leastSingularNorm (E := SymmetricSquare ξ.ker) (F := F) (covectorRestriction S ξ)) ''
    Metric.sphere (0 : E →L[ℝ] ℝ) 1)

end GlobalEmbedding.Paper
