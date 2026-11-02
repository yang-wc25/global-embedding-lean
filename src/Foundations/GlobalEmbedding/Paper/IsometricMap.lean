import GlobalEmbedding.Paper.InducedMetric

/-!
# Isometric maps into Euclidean space

Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition
`defn:phase`, lines 200–205, with the isometric condition used throughout the paper (for
example, Corollary `cor:small-immersion`).

The predicate below records precisely the pointwise metric equation
`γ(F)_x = g_x`. Smoothness of `F` and smoothness and positive definiteness of the source
Riemannian metric are hypotheses at its use sites; they are not replaced by metric-space
isometry or added to this equality predicate.
-/

open Manifold

namespace GlobalEmbedding.Paper

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M]

/-- `F` is isometric for the pointwise source metric `g` when its induced metric agrees with
`g` on every tangent space: `γ(F)_x(v,w) = g_x(v,w)` for every `x`, `v`, and `w`.

At applications, smoothness of `F` and the smooth positive-definite Riemannian metric assumptions
on `g` are supplied explicitly. This definition states the exact infinitesimal pullback metric
equation and does not assert global injectivity or equality of metric-space distances.
Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`, lines
200–205, and the isometric-immersion conclusion in Corollary `cor:small-immersion`.
-/
def isometricMap {N : ℕ}
    (g : ∀ x : M, LinearMap.BilinForm ℝ (TangentSpace I x))
    (F : M → EuclideanSpace ℝ (Fin N)) : Prop :=
  ∀ (x : M) (v w : TangentSpace I x), inducedMetric F x v w = g x v w

end GlobalEmbedding.Paper
