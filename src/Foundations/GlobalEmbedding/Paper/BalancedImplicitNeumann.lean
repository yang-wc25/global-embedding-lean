import GlobalEmbedding.Paper.BalancedNeumannSeries
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Neumann invertibility for the implicit function theorem

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 418–425. DAG node: `balanced-implicit-neumann`.
-/

namespace GlobalEmbedding.Paper

/-- If `‖T‖ < 1`, then `I-T` is continuously invertible, and its continuous inverse is the
operator-norm sum of the Neumann series.

Proof: the complete operator algebra geometric series gives both composition identities.
Apply `ContinuousLinearMap.IsInvertible.of_inverse` to construct the continuous equivalence,
and `ContinuousLinearMap.inverse_eq` to identify its inverse with the series sum.
Source: proof of `lem:balanced`, lines 418–425. -/
theorem balanced_implicit_neumann
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X →L[ℝ] X) (hT : ‖T‖ < 1) :
    (ContinuousLinearMap.id ℝ X - T).IsInvertible ∧
      HasSum (fun k : ℕ ↦ T ^ k) (ContinuousLinearMap.id ℝ X - T).inverse := by
  obtain ⟨hsum, hleft, hright⟩ := balanced_neumann_series_operator T hT
  refine ⟨.of_inverse hleft hright, ?_⟩
  rw [ContinuousLinearMap.inverse_eq hleft hright]
  exact hsum.hasSum

#print axioms balanced_implicit_neumann

end GlobalEmbedding.Paper
