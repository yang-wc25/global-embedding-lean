import GlobalEmbedding.Paper.SymmetricSquareSelfAdjoint
import GlobalEmbedding.Paper.SupportedRankLegalVariation

/-!
# The actual covector square is the original quadratic operator evaluation

Source: original `prop:supported-rank`, equation (9.4), lines 1014–1022.
DAG: `symmetric-square-covector-evaluation`. Exclusive worker W2.
The actual covector-square definition is the accepted W6 provider, reused unchanged.
-/

namespace GlobalEmbedding.Paper
open scoped TensorProduct

/-- The actual square functional equals contraction followed by the SAME covector.
Source: `ξ²(Q)=Q(ξ,ξ)` in the original kernel-graph variation. -/
theorem supportedRankCovectorSquare_eq_contraction
    {E : Type*} [AddCommGroup E] [Module ℝ E] (ξ : E →ₗ[ℝ] ℝ) :
    supportedRankCovectorSquare ξ = ξ.comp (contractionKernelQuotientMap ξ) := by
  apply (symmetricSquareRelations E).linearMap_qext
  apply TensorProduct.ext'
  intro v w
  change supportedRankCovectorSquare ξ (symmetricSquareProduct E v w) =
    ξ (contractionKernelQuotientMap ξ (symmetricSquareProduct E v w))
  rw [supportedRankCovectorSquare_product, contractionKernelQuotientMap_product]
  simp only [map_smul, map_add, smul_eq_mul]
  ring

/-- For the genuine real Riesz covector, the actual square is Q(x,x) of the
SAME equivalent self-adjoint operator. Source: original equation (9.4). -/
theorem supportedRankCovectorSquare_inner_eq_operator
    {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
    [FiniteDimensional ℝ V] (q : SymmetricSquare V) (x : V) :
    supportedRankCovectorSquare (innerₗ V x) q =
      inner ℝ ((symmetricSquareToSelfAdjoint q).val x) x := by
  rw [supportedRankCovectorSquare_eq_contraction]
  change inner ℝ x (contractionKernelQuotientMap (innerₗ V x) q) = _
  rw [← symmetricSquareToSelfAdjoint_apply]
  exact real_inner_comm _ _

end GlobalEmbedding.Paper
