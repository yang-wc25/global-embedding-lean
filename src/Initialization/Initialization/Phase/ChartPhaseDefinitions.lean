import GlobalEmbedding.Offline.ActualHessianJet
import GlobalEmbedding.Paper.BestPhaseSupremum

noncomputable section
open Manifold GlobalEmbedding.Paper GlobalEmbedding.Offline
open scoped ContDiff TensorProduct

namespace GlobalEmbedding.Initialization

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance chartPhaseRelationsClosed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance chartPhaseSquareNormed {E : Type*}
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

/-- The actual normal projection of the actual coordinate Hessian. Its target
is the ambient Euclidean space with the induced normal norm unchanged. -/
def chartNormalSecondJet {N : ℕ} (u : E → EuclideanSpace ℝ (Fin N)) (x : E) :
    SymmetricSquare E →L[ℝ] EuclideanSpace ℝ (Fin N) :=
  (LinearMap.range (fderiv ℝ u x).toLinearMap)ᗮ.starProjection.comp (coordinateHessianJet u x)

/-- The original best-phase operator functional, applied in the specified
chart's Euclidean reference norm to its actual normal second jet. -/
def chartPhaseMargin {N : ℕ} (u : E → EuclideanSpace ℝ (Fin N)) (x : E) : ℝ :=
  bestPhaseSupremum (chartNormalSecondJet u x)


end GlobalEmbedding.Initialization
