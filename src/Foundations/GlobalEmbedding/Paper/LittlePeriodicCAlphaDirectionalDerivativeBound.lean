import GlobalEmbedding.Paper.LittlePeriodicCAlphaDirectionalDerivative

/-!
# The actual little Hölder derivative operator norm

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-little-directional-derivative-bound`.
-/

namespace GlobalEmbedding.Paper

/-- The actual little-space directional derivative has operator norm at most ‖v‖.

Proof: the inherited subtype norms and the actual ambient derivative formula identify the
application bound with the previously proved full Hölder norm contraction. Apply the
continuous-linear-map operator norm criterion. Source: differentiation in `lem:balanced`. -/
theorem littlePeriodicCAlphaDirectionalDerivative_bound {a N k : ℕ} {α : ℝ}
    (v : EuclideanSpace ℝ (Fin a)) :
    ‖littlePeriodicCAlphaDirectionalDerivative (N := N) (k := k) (α := α) v‖ ≤ ‖v‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
  intro f
  exact periodicCAlphaDirectionalDerivative_norm v f.val

#print axioms littlePeriodicCAlphaDirectionalDerivative_bound

end GlobalEmbedding.Paper
