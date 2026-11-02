import Mathlib.Analysis.Calculus.ImplicitContDiff
import Mathlib.Analysis.Complex.Basic

/-!
# Analytic input for the collar's Banach implicit function step

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534. This is the analytic-input part of the holomorphic implicit-function
argument. Converting general Banach-domain Fréchet holomorphy to `AnalyticAt` is a separate
prerequisite and is not assumed to have been proved here.
-/

open scoped Topology ContDiff

namespace GlobalEmbedding.Paper

/-- An analytic Banach-space equation with invertible vertical derivative has a local analytic
branch, the prescribed base value, and uniqueness among nearby solutions.

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition `prop:collar`,
proof lines 530–534, analytic fixed-point dependence; Mathlib `ImplicitContDiff` supplies the
implicit-function construction. Convert the analytic input to `ContDiffAt ℂ ω`, apply Mathlib's
implicit-function equation and uniqueness theorems, and use its preservation of `C^ω` followed
by `ContDiffAt.analyticAt`. Completeness is required by these conversions. No finite-dimensional
parameter hypothesis is needed for this analytic-input prerequisite.
-/
theorem collar_analytic_banach_implicit
    {Z E : Type*} [NormedAddCommGroup Z] [NormedSpace ℂ Z] [CompleteSpace Z]
    [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
    (G : Z × E → E) (z₀ : Z) (x₀ : E)
    (hG : AnalyticAt ℂ G (z₀, x₀)) (hzero : G (z₀, x₀) = 0)
    (hInv : (fderiv ℂ G (z₀, x₀) ∘L ContinuousLinearMap.inr ℂ Z E).IsInvertible) :
    ∃ ψ : Z → E, AnalyticAt ℂ ψ z₀ ∧ ψ z₀ = x₀ ∧
      (∀ᶠ z in 𝓝 z₀, G (z, ψ z) = 0) ∧
      (∀ᶠ v in 𝓝 (z₀, x₀), G v = 0 ↔ ψ v.1 = v.2) := by
  have h : ContDiffAt ℂ ω G (z₀, x₀) := hG.contDiffAt
  have hn : (ω : ℕ∞ω) ≠ 0 := by simp
  refine ⟨h.implicitFunction hn hInv, (h.contDiffAt_implicitFunction hn hInv).analyticAt,
    h.implicitFunction_apply_self hn hInv, ?_, ?_⟩
  · simpa only [hzero] using h.eventually_apply_implicitFunction hn hInv
  · simpa only [hzero] using h.eventually_apply_eq_iff_implicitFunction hn hInv

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collar_analytic_banach_implicit
