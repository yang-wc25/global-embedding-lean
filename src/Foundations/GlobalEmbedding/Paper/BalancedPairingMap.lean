import GlobalEmbedding.Paper.BalancedPairingColumns
import Mathlib.Analysis.InnerProductSpace.LinearMap

/-!
# The full actual first/second pairing operator

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 376.
DAG node: `balanced-pairing-map`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- Pair with every actual first and once-indexed second column, in the full
Euclidean tuple space. No projection onto a column span occurs. -/
noncomputable def balancedPairingMap {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ∀ x : M, TangentSpace I x) (x : M) :
    EuclideanSpace ℝ (Fin N) →L[ℝ] EuclideanSpace ℝ (BalancedPairingIndex a) :=
  ContinuousLinearMap.comp
    (PiLp.continuousLinearEquiv 2 ℝ (fun _ : BalancedPairingIndex a ↦ ℝ)).symm.toContinuousLinearMap
      (ContinuousLinearMap.pi fun i ↦ innerSL ℝ (balancedPairingColumns P D x i))

end GlobalEmbedding.Paper
