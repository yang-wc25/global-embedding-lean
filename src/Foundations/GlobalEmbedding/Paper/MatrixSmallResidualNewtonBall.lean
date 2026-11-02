import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Topology.MetricSpace.Contracting
import GlobalEmbedding.Paper.BalancedImplicitNeumann

/-!
# Quantitative small-residual Newton correction

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
lines 311–315. DAG node: `matrix-small-residual-newton-ball`.
-/

open Set Metric
open scoped Topology NNReal

namespace GlobalEmbedding.Paper

/-- A nonlinear equation with small normalized residual and normalized derivative close to
identity has a unique zero in a fixed ball. Its size is bounded by the actual residual,
and its derivative is invertible there.

Proof: `N x = x - A.symm (f x)` is a quarter contraction on the closed ball by the mean
value inequality. Its value at zero has norm at most half the radius, so it maps the ball
into itself. The complete-subset fixed-point theorem yields its unique fixed point.
The contraction estimate bounds this point by four thirds of the initial residual and
hence by two thirds of the radius. The derivative of `N` has norm below one, so a Neumann
inverse makes the derivative of `f` invertible. Source: `prop:matrix`, lines 311–315;
the explicit constants and Banach-space generality expand the paper's contraction step. -/
theorem small_residual_newton_ball
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X]
    (f : X → X) (A : X ≃L[ℝ] X) (r : ℝ) (hr : 0 < r)
    (hf : ∀ x ∈ closedBall (0 : X) r, DifferentiableAt ℝ f x)
    (hD : ∀ x ∈ closedBall (0 : X) r,
      ‖ContinuousLinearMap.id ℝ X - (A.symm : X →L[ℝ] X).comp (fderiv ℝ f x)‖ ≤ 1 / 4)
    (hres : ‖A.symm (f 0)‖ ≤ r / 2) :
    ∃ x : X, ‖x‖ ≤ r ∧ f x = 0 ∧
      ‖x‖ ≤ (4 / 3 : ℝ) * ‖A.symm (f 0)‖ ∧ ‖x‖ ≤ 2 * r / 3 ∧
      (fderiv ℝ f x).IsInvertible ∧
      ∀ y : X, ‖y‖ ≤ r → f y = 0 → y = x := by
  let N : X → X := fun x ↦ x - A.symm (f x)
  let D : X → X →L[ℝ] X := fun x ↦
    ContinuousLinearMap.id ℝ X - (A.symm : X →L[ℝ] X).comp (fderiv ℝ f x)
  have hN : ∀ x ∈ closedBall (0 : X) r, HasFDerivAt N (D x) x := by
    intro x hx
    exact (hasFDerivAt_id x).sub (A.symm.hasFDerivAt.comp x (hf x hx).hasFDerivAt)
  have hLip : LipschitzOnWith (1 / 4 : ℝ≥0) N (closedBall (0 : X) r) := by
    apply (convex_closedBall (0 : X) r).lipschitzOnWith_of_nnnorm_hasFDerivWithin_le
      (fun x hx ↦ (hN x hx).hasFDerivWithinAt)
    intro x hx
    exact_mod_cast hD x hx
  have hzero : (0 : X) ∈ closedBall (0 : X) r := by simp [hr.le]
  have hNzero : ‖N 0‖ = ‖A.symm (f 0)‖ := by simp [N]
  have hmaps : MapsTo N (closedBall (0 : X) r) (closedBall (0 : X) r) := by
    intro x hx
    rw [mem_closedBall_zero_iff] at hx ⊢
    have hdist := hLip.dist_le_mul x (by simpa using hx) 0 hzero
    have hbound : ‖N x - N 0‖ ≤ (1 / 4 : ℝ) * ‖x‖ := by
      simpa [dist_eq_norm] using hdist
    calc
      ‖N x‖ ≤ ‖N x - N 0‖ + ‖N 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (N x - N 0) (N 0)
      _ ≤ (1 / 4 : ℝ) * ‖x‖ + r / 2 := add_le_add hbound (hNzero ▸ hres)
      _ ≤ r := by linarith
  have hcontract : ContractingWith (1 / 4 : ℝ≥0)
      (hmaps.restrict N (closedBall (0 : X) r) (closedBall (0 : X) r)) := by
    refine ⟨by norm_num, ?_⟩
    intro x y
    exact hLip x.property y.property
  obtain ⟨x, hx, hfix, _, _⟩ := ContractingWith.exists_fixedPoint'
    (isClosed_closedBall.isComplete) hmaps hcontract hzero (edist_ne_top _ _)
  have hfx : f x = 0 := by
    have h : A.symm (f x) = 0 := by
      have := hfix.eq
      dsimp [N] at this
      exact sub_eq_self.mp this
    exact A.symm.injective (by simpa using h)
  have hdist := hLip.dist_le_mul x hx 0 hzero
  have hsize : ‖x‖ ≤ (1 / 4 : ℝ) * ‖x‖ + ‖A.symm (f 0)‖ := by
    calc
      ‖x‖ = ‖N x‖ := by rw [hfix.eq]
      _ ≤ ‖N x - N 0‖ + ‖N 0‖ := by
        simpa only [sub_add_cancel] using norm_add_le (N x - N 0) (N 0)
      _ ≤ (1 / 4 : ℝ) * ‖x‖ + ‖A.symm (f 0)‖ := by
        simpa [dist_eq_norm, hNzero] using add_le_add_right hdist ‖N 0‖
  have hsmall : ‖x‖ ≤ (4 / 3 : ℝ) * ‖A.symm (f 0)‖ := by linarith
  have hinterior : ‖x‖ ≤ 2 * r / 3 := by linarith
  have hdinv : (ContinuousLinearMap.id ℝ X - D x).IsInvertible := by
    exact (balanced_implicit_neumann (D x) (lt_of_le_of_lt (hD x hx) (by norm_num))).1
  have hdid : ContinuousLinearMap.id ℝ X - D x =
      (A.symm : X →L[ℝ] X).comp (fderiv ℝ f x) := by simp [D]
  rw [hdid] at hdinv
  have hfinv : (fderiv ℝ f x).IsInvertible := by
    simpa using hdinv
  refine ⟨x, mem_closedBall_zero_iff.mp hx, hfx, hsmall, hinterior, hfinv, ?_⟩
  intro y hy hfy
  have hyball : y ∈ closedBall (0 : X) r := mem_closedBall_zero_iff.mpr hy
  have hNy : N y = y := by simp [N, hfy]
  have hxy := hLip.dist_le_mul y hyball x hx
  rw [hNy, hfix.eq] at hxy
  have : dist y x = 0 := by
    have := dist_nonneg (x := y) (y := x)
    norm_num at hxy
    linarith
  exact dist_eq_zero.mp this

#print axioms small_residual_newton_ball

end GlobalEmbedding.Paper
