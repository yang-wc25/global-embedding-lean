import GlobalEmbedding.Paper.BalancedPairingMap

/-!
# Arbitrary right inverses of the actual full pairing operator

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 376–414.
DAG node: `balanced-pairing-right-inverse`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- A right inverse on the entire first/second Euclidean data space.
There is no condition on the range of `C`. -/
def IsBalancedPairingRightInverse {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ∀ x : M, TangentSpace I x) (x : M)
    (C : EuclideanSpace ℝ (BalancedPairingIndex a) →L[ℝ]
      EuclideanSpace ℝ (Fin N)) : Prop :=
  (balancedPairingMap P D x).comp C = ContinuousLinearMap.id ℝ _

end GlobalEmbedding.Paper
