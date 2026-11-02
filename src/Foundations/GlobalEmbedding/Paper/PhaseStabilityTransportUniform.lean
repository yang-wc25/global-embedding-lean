import GlobalEmbedding.Paper.PhaseStabilityTransport

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
`prop:initialization`, uniform coefficient transport and preservation of the selector margin. -/

namespace GlobalEmbedding.Paper
open SymmetricSquareNorms
attribute [local instance] squareSemi squareTopology squareAddMonoid squareNS squareModule
variable {E F W : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [InnerProductSpace ℝ F]
  [SeminormedAddCommGroup W] [NormedSpace ℝ W]

/-- Uniform transport retains a positive margin with denominator `1 + L²`, including
zero-dimensional source spaces. Only the inverse norm bound is needed.
Proof: the squared inverse norm is bounded by `L²`, and apply the positive-denominator
transport theorem with `C = 1 + L²`.
Source: `prop:initialization`, uniform invertible coefficient matrix and selector margin. -/
theorem phase_stability_transport_uniform_lower_bound (e : E ≃L[ℝ] F)
    (S : SymmetricSquare F →L[ℝ] W) (S' : SymmetricSquare E →L[ℝ] W)
    (m L : ℝ) (hm : 0 < m) (hinv : ‖e.symm.toContinuousLinearMap‖ ≤ L)
    (hS : ∀ z, m * ‖z‖ ≤ ‖S z‖)
    (herr : ‖S' - S.comp (symmetricSquareMapL e.toContinuousLinearMap)‖ <
      m / (2 * (1 + L ^ 2))) :
    (∀ z, (m / (1 + L ^ 2)) * ‖z‖ ≤
      ‖S (symmetricSquareMap e.toContinuousLinearMap z)‖) ∧
    (∀ z, (m / (2 * (1 + L ^ 2))) * ‖z‖ ≤ ‖S' z‖) := by
  have hL : 0 ≤ L := (norm_nonneg e.symm.toContinuousLinearMap).trans hinv
  have hsq : ‖e.symm.toContinuousLinearMap‖ ^ 2 ≤ 1 + L ^ 2 := by
    nlinarith [norm_nonneg e.symm.toContinuousLinearMap]
  exact phase_stability_transport_lower_bound e S S' m (1 + L ^ 2) hm
    (by positivity) hsq hS herr

end GlobalEmbedding.Paper
