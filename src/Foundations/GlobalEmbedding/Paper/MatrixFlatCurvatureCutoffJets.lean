import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Calculus.ContDiff.Comp

/-!
# The actual flat curvature cutoff and its vanishing jets

Source: `literature/parallelizable-stable-plus-one/main.tex`, `prop:matrix` proof,
lines 299–300. DAG node: `matrix-flat-curvature-cutoff-jets`.
-/

open Polynomial
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual source cutoff is smooth and nonnegative, vanishes exactly at zero curvature,
and every Frechet jet vanishes there.

Proof: derivatives of `expNegInvGlue` are polynomial-in-inverse multiples of itself, by
Mathlib's explicit derivative recurrence. Thus all scalar derivatives and all scalar
Frechet derivatives vanish at zero. The Faà di Bruno formula for the composition with
`κ²` is a finite sum with an outer derivative as a factor, so every term vanishes at
zero curvature. Smoothness and positivity are native properties of `expNegInvGlue`.
Source: `prop:matrix` proof, lines 299–300. -/
theorem flat_curvature_cutoff_jets
    {P : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P]
    (κ : P → ℝ) (hκ : ContDiff ℝ ∞ κ) :
    ContDiff ℝ ∞ (fun x ↦ expNegInvGlue (κ x ^ 2)) ∧
      (∀ x, 0 ≤ expNegInvGlue (κ x ^ 2) ∧
        (expNegInvGlue (κ x ^ 2) = 0 ↔ κ x = 0)) ∧
      ∀ x, κ x = 0 → ∀ n : ℕ,
        iteratedFDeriv ℝ n (fun y ↦ expNegInvGlue (κ y ^ 2)) x = 0 := by
  have hpoly (n : ℕ) (p : ℝ[X]) : ∃ q : ℝ[X],
      iteratedDeriv n (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) =
        fun x ↦ q.eval x⁻¹ * expNegInvGlue x := by
    induction n generalizing p with
    | zero => exact ⟨p, iteratedDeriv_zero⟩
    | succ n ih =>
      obtain ⟨q, hq⟩ := ih (X ^ 2 * (p - derivative p))
      refine ⟨q, ?_⟩
      rw [iteratedDeriv_succ']
      have hd : deriv (fun x ↦ p.eval x⁻¹ * expNegInvGlue x) =
          fun x ↦ (X ^ 2 * (p - derivative p)).eval x⁻¹ * expNegInvGlue x := by
        funext x
        exact (expNegInvGlue.hasDerivAt_polynomial_eval_inv_mul p x).deriv
      rw [hd, hq]
  have hχ (n : ℕ) : iteratedFDeriv ℝ n expNegInvGlue 0 = 0 := by
    apply norm_eq_zero.mp
    rw [norm_iteratedFDeriv_eq_norm_iteratedDeriv]
    obtain ⟨q, hq⟩ := hpoly n 1
    have hz : iteratedDeriv n expNegInvGlue 0 = 0 := by
      have h := congrFun hq 0
      simpa using h
    simp [hz]
  have hsquare : ContDiff ℝ ∞ (fun x ↦ κ x ^ 2) := hκ.pow 2
  refine ⟨expNegInvGlue.contDiff.comp hsquare, ?_, ?_⟩
  · intro x
    refine ⟨expNegInvGlue.nonneg _, ?_⟩
    rw [expNegInvGlue.zero_iff_nonpos]
    exact ⟨fun h ↦ by nlinarith, fun h ↦ by simp [h]⟩
  · intro x hx n
    change iteratedFDeriv ℝ n (expNegInvGlue ∘ (fun y ↦ κ y ^ 2)) x = 0
    rw [iteratedFDeriv_comp (expNegInvGlue.contDiff.contDiffAt) hsquare.contDiffAt
      (show (n : ℕ∞ω) ≤ ∞ by simp)]
    ext v
    simp only [hx, zero_pow (show 2 ≠ 0 by norm_num),
      FormalMultilinearSeries.taylorComp, sum_apply,
      FormalMultilinearSeries.compAlongOrderedFinpartition_apply, ftaylorSeries, hχ,
      zero_apply, Finset.sum_const_zero]

#print axioms flat_curvature_cutoff_jets

end GlobalEmbedding.Paper
