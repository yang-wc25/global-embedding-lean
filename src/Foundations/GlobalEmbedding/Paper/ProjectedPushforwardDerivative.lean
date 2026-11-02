import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`,
Definition `defn:phase`, true normal second forms. -/

open Filter
open scoped Topology ContDiff
namespace GlobalEmbedding.Paper

/-- Projecting the derivative of a pushed-forward field kills the derivative of the
field components, leaving the coordinate Hessian. Source: `defn:phase`. -/
theorem general_projected_derivative_of_pushforward
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F]
    (f : E → F) (Y : E → E) (P : F →L[ℝ] F) (x : E)
    (hf : ContDiffAt ℝ 2 f x) (hY : DifferentiableAt ℝ Y x)
    (hP : ∀ z : E, P (fderiv ℝ f x z) = 0) (v : E) :
    P (fderiv ℝ (fun y ↦ fderiv ℝ f y (Y y)) x v) =
      P (fderiv ℝ (fderiv ℝ f) x v (Y x)) := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) x :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  rw [fderiv_clm_apply hf' hY]
  simp only [add_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.flip_apply,
    map_add, hP, zero_add]

end GlobalEmbedding.Paper
