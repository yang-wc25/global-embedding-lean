import GlobalEmbedding.Paper.SymmetricSquareTransportLowerBound
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

/-- A perturbation by at most half the transported lower bound retains half that bound.
Proof: the reverse triangle inequality subtracts the perturbation error from the transported
lower bound. This pointwise estimate applies also to zero-dimensional symmetric squares.
Source: `prop:initialization`, stability of the good hyperplane. -/
theorem symmetricSquare_transport_perturbation {W : Type*} [SeminormedAddCommGroup W]
    [NormedSpace ℝ W] (e : E ≃L[ℝ] F) (S : SymmetricSquare F →ₗ[ℝ] W)
    (S' : SymmetricSquare E →ₗ[ℝ] W) (m C : ℝ) (hm : 0 ≤ m) (hC : 0 < C)
    (hinv : ‖e.symm.toContinuousLinearMap‖ ^ 2 ≤ C)
    (hS : ∀ z, m * ‖z‖ ≤ ‖S z‖)
    (herr : ∀ z, ‖S' z - S (symmetricSquareMap e.toContinuousLinearMap z)‖ ≤
      (m / (2 * C)) * ‖z‖) (z : SymmetricSquare E) :
    (m / (2 * C)) * ‖z‖ ≤ ‖S' z‖ := by
  have hbase := symmetricSquare_transport_lower_bound e S m C hm hC hinv hS z
  have htri : ‖S (symmetricSquareMap e.toContinuousLinearMap z)‖ ≤
      ‖S' z‖ + ‖S' z - S (symmetricSquareMap e.toContinuousLinearMap z)‖ := by
    calc
      _ = ‖S' z - (S' z - S (symmetricSquareMap e.toContinuousLinearMap z))‖ := by
        congr 1; abel
      _ ≤ _ := norm_sub_le _ _
  have hhalf : m / C = 2 * (m / (2 * C)) := by field_simp
  rw [hhalf] at hbase
  have he := herr z
  nlinarith

end GlobalEmbedding.Paper
