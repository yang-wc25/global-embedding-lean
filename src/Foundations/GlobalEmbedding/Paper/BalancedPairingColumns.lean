import GlobalEmbedding.Paper.BalancedGeometry

/-!
# Actual first and symmetric second pairing columns

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 376.
DAG node: `balanced-pairing-columns`.
-/

open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- First columns, followed by the lexicographically ordered pairs `i ≤ j`.
Both repeated indices and the empty family are retained. -/
abbrev BalancedPairingIndex (a : ℕ) :=
  Fin a ⊕ {p : Fin a × Fin a // p.1 ≤ p.2}

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- The genuine Euclidean-valued derivative along a tangent vector field.
The target tangent identification is precisely the one in `balancedGeometry`.
No source-fiber norm or connection is introduced. -/
noncomputable def balancedDirectionalDerivative {N : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N)) (D : ∀ x : M, TangentSpace I x)
    (x : M) : EuclideanSpace ℝ (Fin N) :=
  tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) (P x)
    (mfderiv I 𝓘(ℝ, EuclideanSpace ℝ (Fin N)) P x (D x))

/-- The actual first and second derivative columns of `P` along `D`.
The second column indexed by `(i,j)` is literally `D_i(D_j P)`.
Commutativity, when needed to exchange indices, is a separate assertion. -/
noncomputable def balancedPairingColumns {N a : ℕ}
    (P : M → EuclideanSpace ℝ (Fin N))
    (D : Fin a → ∀ x : M, TangentSpace I x) (x : M) :
    BalancedPairingIndex a → EuclideanSpace ℝ (Fin N)
  | Sum.inl i => balancedDirectionalDerivative P (D i) x
  | Sum.inr ij => balancedDirectionalDerivative
      (balancedDirectionalDerivative P (D ij.val.2)) (D ij.val.1) x

end GlobalEmbedding.Paper
