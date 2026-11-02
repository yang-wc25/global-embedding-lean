import Mathlib.Analysis.SpecificLimits.Normed
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# Operator Neumann series

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 418–425. DAG node: `balanced-neumann-series-operator`.
-/

namespace GlobalEmbedding.Paper

/-- The Neumann series converges in operator norm and is a two-sided inverse to `I - T`.

Proof: apply the geometric series theorem in the complete normed ring of continuous linear
endomorphisms. Its two multiplication identities are precisely the required compositions.
Source: proof of `lem:balanced`, lines 418–425. -/
theorem balanced_neumann_series_operator
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X →L[ℝ] X) (hT : ‖T‖ < 1) :
    Summable (fun k : ℕ ↦ T ^ k) ∧
      (ContinuousLinearMap.id ℝ X - T).comp (∑' k : ℕ, T ^ k) =
        ContinuousLinearMap.id ℝ X ∧
      (∑' k : ℕ, T ^ k).comp (ContinuousLinearMap.id ℝ X - T) =
        ContinuousLinearMap.id ℝ X := by
  exact ⟨summable_geometric_of_norm_lt_one hT,
    mul_neg_geom_series T hT, geom_series_mul_neg T hT⟩

#print axioms balanced_neumann_series_operator

end GlobalEmbedding.Paper
