import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.Normed.Module.RCLike.Real

/-!
# Derivatives preserve a closed real target subspace on a ball

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This supplies real-form preservation for the complex derivative of the
fixed-point equation, including when the original real fixed point lies on the ball boundary.
-/

open scoped Topology

namespace GlobalEmbedding.Paper

/-- If a C¹ real map takes a positive-radius closed ball into a closed real subspace, then its
Fréchet derivative at any point of that ball also takes values in that subspace.

Source: Proposition `prop:collar`, proof lines 530–534, real-form analytic fixed-point step.
At an interior point x, each line x+t v stays in the ball for t sufficiently small. Its difference
quotients belong to the real subspace because both function values do and the subspace is linear.
Their limit is Df(x)v, so closedness puts that derivative in the same subspace. For a fixed v,
the map x↦Df(x)v is continuous by C¹ regularity. The inverse image of the closed subspace is closed
and contains the open ball, hence contains its closure, the closed ball. This proves the boundary
case without assuming the fixed point belongs to the interior.
-/
theorem collar_closed_submodule_derivative
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (hf : ContDiff ℝ 1 f) (R : Submodule ℝ F) (hR : IsClosed (R : Set F))
    (c : E) (r : ℝ) (hr : 0 < r)
    (hmap : Set.MapsTo f (Metric.closedBall c r) R) :
    ∀ x ∈ Metric.closedBall c r, ∀ v : E, fderiv ℝ f x v ∈ R := by
  intro x hx v
  have hinner : Metric.ball c r ⊆ {y : E | fderiv ℝ f y v ∈ R} := by
    intro y hy
    have hline : HasDerivAt (fun t : ℝ ↦ f (y + t • v)) (fderiv ℝ f y v) 0 := by
      have hpath : HasDerivAt (fun t : ℝ ↦ y + t • v) v 0 := by
        simpa using (hasDerivAt_id (0 : ℝ)).smul_const v |>.const_add y
      apply (hf.differentiable one_ne_zero y).hasFDerivAt.comp_hasDerivAt_of_eq 0 hpath
      simp
    have hpath : ContinuousAt (fun t : ℝ ↦ y + t • v) 0 := by fun_prop
    have hball : Metric.closedBall c r ∈ 𝓝 (y + (0 : ℝ) • v) := by
      simpa only [zero_smul, add_zero] using Metric.closedBall_mem_nhds_of_mem hy
    have hnear₀ : ∀ᶠ t : ℝ in 𝓝 0, y + t • v ∈ Metric.closedBall c r :=
      hpath.eventually_mem hball
    have hnear : ∀ᶠ t : ℝ in 𝓝[≠] 0, y + t • v ∈ Metric.closedBall c r :=
      hnear₀.filter_mono nhdsWithin_le_nhds
    apply hR.mem_of_tendsto hline.tendsto_slope
    filter_upwards [hnear] with t ht
    simp only [slope_def_module, sub_zero, zero_smul, add_zero]
    exact R.smul_mem _ (R.sub_mem (hmap ht) (hmap (Metric.ball_subset_closedBall hy)))
  have hclosed : IsClosed {y : E | fderiv ℝ f y v ∈ R} :=
    hR.preimage (((hf.continuous_fderiv one_ne_zero).clm_apply continuous_const))
  have hclosure := closure_minimal hinner hclosed
  rw [closure_ball c hr.ne'] at hclosure
  exact hclosure hx

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_closed_submodule_derivative
