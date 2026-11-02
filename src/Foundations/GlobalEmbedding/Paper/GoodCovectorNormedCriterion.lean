import GlobalEmbedding.Paper.GoodCovector
import GlobalEmbedding.Paper.SymmetricSquareLinearMapEquality
import GlobalEmbedding.Paper.TrueSecondFormL
import GlobalEmbedding.Paper.CovectorRestriction

open Bundle Manifold
open scoped TensorProduct ContDiff

namespace GlobalEmbedding.Paper

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

private local instance goodSquareRelationsClosed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] :
    IsClosed (symmetricSquareRelations E : Set (E ⊗[ℝ] E)) :=
  Submodule.closed_of_finiteDimensional _

private noncomputable local instance goodSquareNormed {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E] [FiniteDimensional ℝ E] : NormedAddCommGroup (SymmetricSquare E) :=
  Submodule.Quotient.normedAddCommGroup (symmetricSquareRelations E)

/-- The norm-independent source good-covector predicate is exactly the actual
normed kernel restriction criterion used in phase stability, for every supplied
auxiliary tangent metric. Proof: the entire algebraic kernel inclusion equals
the canonical normed quotient map, and trueSecondFormL has the actual original
linear map. Source: `defn:phase`, actual good covectors. -/
theorem good_covector_iff_normed
    {E H M : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    [BoundarylessManifold I M] [RiemannianBundle (TangentSpace I : M → Type _)] {N : ℕ}
    (f : M → EuclideanSpace ℝ (Fin N))
    (hf : ContMDiff I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) ∞ f) (x : M)
    (ξ : TangentSpace I x →L[ℝ] ℝ) :
    GoodCovector f hf x ξ ↔ ξ ≠ 0 ∧ Function.Injective
      (covectorRestriction (E := TangentSpace I x) (F := normalSpace (I := I) f x)
        (trueSecondFormL f hf x) ξ) := by
  unfold GoodCovector
  have hmap := symmetric_square_linear_map_eq (E := ξ.ker) (F := TangentSpace I x) ξ.ker.subtypeL
  change symmetricSquareLinearMap ξ.ker.subtype = symmetricSquareMap ξ.ker.subtypeL at hmap
  rw [hmap]
  have hfun : ((trueSecondForm f hf x).comp (symmetricSquareMap ξ.ker.subtypeL) :
      SymmetricSquare ξ.ker → normalSpace (I := I) f x) =
      covectorRestriction (E := TangentSpace I x) (F := normalSpace (I := I) f x)
        (trueSecondFormL f hf x) ξ := by
    funext z
    simp only [covectorRestriction, ContinuousLinearMap.comp_apply, trueSecondFormL,
      LinearMap.coe_toContinuousLinearMap', LinearMap.comp_apply, symmetricSquareMapL_apply]
  rw [hfun]

end GlobalEmbedding.Paper
