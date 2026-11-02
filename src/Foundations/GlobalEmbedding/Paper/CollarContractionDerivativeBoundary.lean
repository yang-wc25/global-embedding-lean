import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Derivative bound at the boundary of an invariant contraction ball

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. The analytic implicit-function route to the real contraction fixed point
must allow the fixed point to lie on the boundary of its original closed invariant ball.
-/

open scoped NNReal

namespace GlobalEmbedding.Paper

/-- A continuously differentiable real map which is `q`-Lipschitz on a positive-radius closed
ball has derivative norm at most `q` everywhere on that ball, including its boundary.

Source: Proposition `prop:collar`, proof lines 530–534, expanded boundary case in the analytic
fixed-point argument. At each point of the open ball, the closed ball is a neighborhood, so
Mathlib's converse mean-value bound applies. The derivative norm is continuous for a C¹ map;
its closed sublevel set contains the open ball and hence its closure, which is the closed ball
when the radius is positive. The target may differ from the domain, as needed for a real form
included in a complex Banach space. No nontriviality or finite-dimensionality is required.
-/
theorem collar_contraction_derivative_boundary
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (c : E) (r : ℝ) (hr : 0 < r)
    (q : ℝ≥0) (hlip : LipschitzOnWith q f (Metric.closedBall c r)) :
    ∀ x ∈ Metric.closedBall c r, ‖fderiv ℝ f x‖ ≤ q := by
  have hinner : Metric.ball c r ⊆ {x : E | ‖fderiv ℝ f x‖ ≤ q} := by
    intro x hx
    exact norm_fderiv_le_of_lipschitzOn ℝ (Metric.closedBall_mem_nhds_of_mem hx) hlip
  have hclosed : IsClosed {x : E | ‖fderiv ℝ f x‖ ≤ q} :=
    isClosed_le (hf.continuous_fderiv one_ne_zero).norm continuous_const
  have hclosure := closure_minimal hinner hclosed
  rw [closure_ball c hr.ne'] at hclosure
  exact hclosure

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_contraction_derivative_boundary
