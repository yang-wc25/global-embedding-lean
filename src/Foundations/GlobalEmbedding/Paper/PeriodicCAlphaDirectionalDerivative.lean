import GlobalEmbedding.Paper.PeriodicCAlphaFunction
import GlobalEmbedding.Paper.DirectionalDerivativeBound
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Actual raw periodic Hölder directional derivative

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 399–418.
DAG node: `balanced-holder-raw-directional-derivative`.
-/

open Set WithLp

namespace GlobalEmbedding.Paper

/-- Construct the actual directional derivative from periodic C^{k+1,α} to periodic C^{k,α}.

The underlying lift is exactly x↦Df(x)v. Differentiating the actual integer periodicity gives
periodicity, and C^{k+1} calculus gives C^k regularity. The proved fixed-direction tensor
contraction bound transfers every finite derivative and Holder witness from the next jet.
Source: bounded spatial differentiation in the proof of `lem:balanced`. -/
noncomputable def periodicCAlphaDirectionalDerivative {a N k : ℕ} {α : ℝ}
    (v : EuclideanSpace ℝ (Fin a)) (f : PeriodicCAlphaFunction a N (k + 1) α) :
    PeriodicCAlphaFunction a N k α where
  toFun x := fderiv ℝ f.toFun x v
  periodic := by
    intro x n
    have heq : (fun z ↦ f.toFun (z + toLp 2 (fun i ↦ (n i : ℝ)))) = f.toFun :=
      funext (fun z ↦ f.periodic z n)
    have ht := fderiv_comp_add_right (𝕜 := ℝ) (f := f.toFun) (x := x)
      (toLp 2 (fun i ↦ (n i : ℝ)))
    rw [heq] at ht
    exact congrArg (fun G ↦ G v) ht.symm
  contDiff := (f.contDiff.fderiv_right (by norm_cast)).clm_apply contDiff_const
  derivative_bounded := by
    intro j hj
    obtain ⟨C, hC⟩ := f.derivative_bounded (j + 1) (Nat.add_le_add_right hj 1)
    refine ⟨‖v‖ * C, ?_⟩
    intro x hx
    have hbound := (directional_derivative_iterated_bound j f.toFun
      (f.contDiff.of_le (by exact_mod_cast Nat.add_le_add_right hj 1)) v x x).1
    exact hbound.trans (mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _))
  holder_bounded := by
    obtain ⟨C, hC⟩ := f.holder_bounded
    refine ⟨‖v‖ * C, ?_⟩
    intro x y d hd
    have hbound := (directional_derivative_iterated_bound k f.toFun f.contDiff v x y).2
    calc
      _ ≤ (‖v‖ * ‖iteratedFDeriv ℝ (k + 1) f.toFun x -
          iteratedFDeriv ℝ (k + 1) f.toFun y‖) / d ^ α :=
        div_le_div_of_nonneg_right hbound (Real.rpow_nonneg hd.le _)
      _ = ‖v‖ * (‖iteratedFDeriv ℝ (k + 1) f.toFun x -
          iteratedFDeriv ℝ (k + 1) f.toFun y‖ / d ^ α) := mul_div_assoc _ _ _
      _ ≤ ‖v‖ * C := mul_le_mul_of_nonneg_left (hC x y hd) (norm_nonneg _)

#print axioms periodicCAlphaDirectionalDerivative

end GlobalEmbedding.Paper
