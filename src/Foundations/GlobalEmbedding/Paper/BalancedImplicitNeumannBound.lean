import GlobalEmbedding.Paper.BalancedImplicitNeumann

/-!
# Uniform quantitative Neumann bound for the actual implicit derivative inverse

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, line 418.
DAG node: `balanced-implicit-neumann-uniform-bound`.
-/

namespace GlobalEmbedding.Paper

/-- A common strict operator bound gives a common quantitative bound for the actual inverse.

The accepted Neumann theorem supplies invertibility and identifies the actual continuous
inverse with the operator-norm series. Apply Mathlib's geometric-series norm bound, which
allows a zero space, use the identity norm bound ≤1, and compare the positive reciprocals.
Source: the same Neumann bound for highest unknowns in the proof of `lem:balanced`. -/
theorem balanced_implicit_neumann_uniform_bound
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (T : X →L[ℝ] X) {q : ℝ} (hT : ‖T‖ ≤ q) (hq : q < 1) :
    (ContinuousLinearMap.id ℝ X - T).IsInvertible ∧
      ‖(ContinuousLinearMap.id ℝ X - T).inverse‖ ≤ (1 - q)⁻¹ := by
  obtain ⟨hi, hsum⟩ := balanced_implicit_neumann T (hT.trans_lt hq)
  refine ⟨hi, ?_⟩
  rw [← hsum.tsum_eq]
  calc
    ‖∑' n : ℕ, T ^ n‖ ≤ ‖(1 : X →L[ℝ] X)‖ - 1 + (1 - ‖T‖)⁻¹ :=
      tsum_geometric_le_of_norm_lt_one T (hT.trans_lt hq)
    _ ≤ (1 - ‖T‖)⁻¹ := by
      have hid : ‖(1 : X →L[ℝ] X)‖ ≤ 1 := ContinuousLinearMap.norm_id_le
      linarith
    _ ≤ (1 - q)⁻¹ := by
      exact inv_anti₀ (sub_pos.mpr hq) (sub_le_sub_left hT 1)

#print axioms balanced_implicit_neumann_uniform_bound

end GlobalEmbedding.Paper
