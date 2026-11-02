import GlobalEmbedding.Paper.SymmetricSquareInverseBound
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

/-- A lower bound survives transport, with every positive upper bound on the squared
inverse norm as denominator. This includes the exact squared inverse norm whenever positive.
Proof: apply the inverse norm estimate and then the given lower bound.
Source: `prop:initialization`, fixed fraction of the selector margin. -/
theorem symmetricSquare_transport_lower_bound {W : Type*} [SeminormedAddCommGroup W]
    [NormedSpace ℝ W] (e : E ≃L[ℝ] F) (S : SymmetricSquare F →ₗ[ℝ] W)
    (m C : ℝ) (hm : 0 ≤ m) (hC : 0 < C)
    (hinv : ‖e.symm.toContinuousLinearMap‖ ^ 2 ≤ C)
    (hS : ∀ z, m * ‖z‖ ≤ ‖S z‖) (z : SymmetricSquare E) :
    (m / C) * ‖z‖ ≤ ‖S (symmetricSquareMap e.toContinuousLinearMap z)‖ := by
  rw [div_mul_eq_mul_div, div_le_iff₀ hC]
  have hi := symmetricSquareMap_inverse_norm_bound e z
  have hnorm : ‖z‖ ≤ C * ‖symmetricSquareMap e.toContinuousLinearMap z‖ :=
    hi.trans (mul_le_mul_of_nonneg_right hinv (norm_nonneg (symmetricSquareMap e.toContinuousLinearMap z)))
  have hmul := mul_le_mul_of_nonneg_left hnorm hm
  have hl := mul_le_mul_of_nonneg_left (hS (symmetricSquareMap e.toContinuousLinearMap z))
    hC.le
  nlinarith

end GlobalEmbedding.Paper
