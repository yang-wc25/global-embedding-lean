import GlobalEmbedding.Paper.BalancedNeumannSeries
import Mathlib.Topology.Algebra.Module.ContinuousLinearMap.Invertible

/-!
# Uniqueness of small quadratic fixed points

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
lines 418–425, agent expansion of quadratic fixed-point uniqueness.
DAG node: `balanced-fixed-small-unique`.
-/

namespace GlobalEmbedding.Paper

/-- Two symmetric quadratic fixed points satisfying the strict linearized smallness bound
coincide, with no assumption that they belong to a prescribed common ball.

Proof: their difference is `(AQ(u,·)+AQ(v,·))(u-v)`. The operator on the right has norm
less than one, since each summand has norm less than one half. The Neumann series implies
that its difference from the identity is injective, so `u-v=0`.
Source: `lem:balanced`, proof, lines 418–425, implicit-branch expansion. -/
theorem balanced_fixed_small_unique {X Y : Type*}
    [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (Q : X →L[ℝ] X →L[ℝ] Y) (hQ : ∀ x y, Q x y = Q y x)
    (A : Y →L[ℝ] X) (f u v : X)
    (hu : u = f + A (Q u u)) (hv : v = f + A (Q v v))
    (hus : ‖(2 : ℝ) • A.comp (Q u)‖ < 1)
    (hvs : ‖(2 : ℝ) • A.comp (Q v)‖ < 1) : u = v := by
  have hsu : ‖A.comp (Q u)‖ < 1 / 2 := by
    rw [norm_smul, Real.norm_ofNat] at hus
    linarith
  have hsv : ‖A.comp (Q v)‖ < 1 / 2 := by
    rw [norm_smul, Real.norm_ofNat] at hvs
    linarith
  let T := A.comp (Q u) + A.comp (Q v)
  have hT : ‖T‖ < 1 := lt_of_le_of_lt (norm_add_le _ _) (by linarith)
  have hdiff : u - v = T (u - v) := by
    calc
      u - v = (f + A (Q u u)) - (f + A (Q v v)) := congrArg₂ (· - ·) hu hv
      _ = A (Q u u) - A (Q v v) := by abel
      _ = T (u - v) := by
        simp only [T, add_apply, ContinuousLinearMap.comp_apply,
          map_sub, hQ v u]
        abel
  obtain ⟨_, hleft, hright⟩ := balanced_neumann_series_operator T hT
  apply sub_eq_zero.mp
  apply (ContinuousLinearMap.IsInvertible.of_inverse hleft hright).injective
  simp only [sub_apply, ContinuousLinearMap.id_apply, map_zero]
  exact sub_eq_zero.mpr hdiff


#print axioms balanced_fixed_small_unique

end GlobalEmbedding.Paper
