import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.Comp
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Calculus.ContDiff.Comp

open Filter
open scoped ContDiff Topology

/-! Source: `literature/parallelizable-stable-plus-one/main.tex`, Definition `defn:phase`. -/

namespace GlobalEmbedding.Paper

variable {E G F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup G] [NormedSpace ℝ G]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Under a C² coordinate change, a projection which annihilates the first derivative of `f`
removes the extra term in the second-order chain rule.

Proof: Differentiate the chain rule twice. The Hessian of `f ∘ h` is the Hessian of `f`
applied to the two derivatives of `h`, plus the first derivative of `f` applied to the Hessian
of `h`. The latter lies in the first-derivative range and is killed by `P`.
Source: Definition `defn:phase`, lines 200–204. -/
theorem projected_hessian_chain (f : E → F) (h : G → E) (P : F →L[ℝ] F) (x : G)
    (hf : ContDiffAt ℝ 2 f (h x)) (hh : ContDiffAt ℝ 2 h x)
    (hP : ∀ z : E, P (fderiv ℝ f (h x) z) = 0) (v w : G) :
    P (fderiv ℝ (fderiv ℝ (f ∘ h)) x v w) =
      P (fderiv ℝ (fderiv ℝ f) (h x) (fderiv ℝ h x v) (fderiv ℝ h x w)) := by
  have hf' : DifferentiableAt ℝ (fderiv ℝ f) (h x) :=
    (hf.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh' : DifferentiableAt ℝ (fderiv ℝ h) x :=
    (hh.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hh0 : DifferentiableAt ℝ h x := hh.differentiableAt (by norm_num)
  have heq : (fun y ↦ fderiv ℝ (f ∘ h) y) =ᶠ[𝓝 x]
      (fun y ↦ (fderiv ℝ f (h y)).comp (fderiv ℝ h y)) := by
    filter_upwards [hh.eventually (by norm_num),
      hh.continuousAt.eventually (hf.eventually (by norm_num))] with y hyh hyf
    exact fderiv_comp y (hyf.differentiableAt (by norm_num)) (hyh.differentiableAt (by norm_num))
  rw [heq.fderiv_eq, fderiv_clm_comp (c := fun y ↦ fderiv ℝ f (h y)) (hf'.comp x hh0) hh',
    fderiv_fun_comp x hf' hh0]
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, map_add, hP, zero_add]

end GlobalEmbedding.Paper
