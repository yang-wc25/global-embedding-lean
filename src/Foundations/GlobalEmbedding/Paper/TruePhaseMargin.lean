import GlobalEmbedding.Paper.TrueSecondFormL
import GlobalEmbedding.Paper.BestPhaseSupremum

open Bundle Manifold
open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance trueMarginSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance trueMarginSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

variable {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}

/-- The best-phase margin of the actual true normal second form. For tangent
dimension at least two its defining supremum is attained, as proved separately.
All norms are the fixed auxiliary tangent Hilbert norm, its tensor quotient norm,
and the induced Euclidean normal-space norm. Source: `defn:phase`. -/
noncomputable def truePhaseMargin (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M) : ℝ :=
  bestPhaseSupremum (trueSecondFormL f hf x)

/-- A uniform positive actual phase margin on a specified indexed family of
chart subsets. Source: `prop:initialization`, uniform selector margin. -/
def HasUniformTruePhaseMargin {ι : Type*} (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f)
    (charts : ι → Set M) (m : ℝ) : Prop :=
  0 < m ∧ ∀ i, ∀ x ∈ charts i, m ≤ truePhaseMargin f hf x

end GlobalEmbedding.Paper
