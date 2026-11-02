import GlobalEmbedding.Paper.SymmetricSquareMapLEval
import GlobalEmbedding.Paper.SymmetricSquareTransportPerturbation
import GlobalEmbedding.Paper.SymmetricSquareNorms

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, second-jet comparison and preservation of the selector margin.
Norms are the canonical Hilbert tensor norm followed by the existing binary quotient norm. -/

open scoped TensorProduct
namespace GlobalEmbedding.Paper

variable {E F G : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [NormedAddCommGroup G] [InnerProductSpace ℝ G]

open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule

/-- The operator norm perturbation criterion gives the required half-margin estimate.
The chosen denominator is any positive bound for the squared inverse norm, so this includes
that exact squared norm in every nonzero-dimensional case.
Source: `prop:initialization`, stability of the good hyperplane after second-jet comparison. -/
theorem phase_stability_transport_lower_bound {W : Type*} [SeminormedAddCommGroup W]
    [NormedSpace ℝ W] (e : E ≃L[ℝ] F) (S : SymmetricSquare F →L[ℝ] W)
    (S' : SymmetricSquare E →L[ℝ] W) (m C : ℝ) (hm : 0 < m) (hC : 0 < C)
    (hinv : ‖e.symm.toContinuousLinearMap‖ ^ 2 ≤ C)
    (hS : ∀ z, m * ‖z‖ ≤ ‖S z‖)
    (herr : ‖S' - S.comp (symmetricSquareMapL e.toContinuousLinearMap)‖ < m / (2 * C)) :
    (∀ z, (m / C) * ‖z‖ ≤ ‖S (symmetricSquareMap e.toContinuousLinearMap z)‖) ∧
    (∀ z, (m / (2 * C)) * ‖z‖ ≤ ‖S' z‖) := by
  refine ⟨symmetricSquare_transport_lower_bound e S.toLinearMap m C hm.le hC hinv hS, ?_⟩
  apply symmetricSquare_transport_perturbation e S.toLinearMap S'.toLinearMap m C hm.le hC hinv hS
  intro z
  have hbound := (S' - S.comp (symmetricSquareMapL e.toContinuousLinearMap)).le_opNorm z
  have hmul := mul_le_mul_of_nonneg_right herr.le (norm_nonneg z)
  simpa only [sub_apply, ContinuousLinearMap.comp_apply,
    symmetricSquareMapL_apply, ContinuousLinearMap.coe_coe] using hbound.trans hmul

end GlobalEmbedding.Paper
