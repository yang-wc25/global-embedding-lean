import GlobalEmbedding.Paper.PeriodicCAlphaFunction
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Pointwise linear closure of the actual periodic Hölder carrier

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of `lem:balanced`,
line 382. DAG node: `balanced-holder-carrier-linear-closure`.
-/

open Set WithLp
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The actual raw periodic Hölder functions contain zero and are closed under pointwise
addition and real scalar multiplication.

Proof: zero has zero derivatives. For sums, add derivative bounds and use the norm triangle
inequality for the top derivative differences and their positive-distance quotients. For
scalar multiples, scale all bounds by the scalar norm. Periodicity and classical regularity
are preserved by these pointwise operations.
Source: `lem:balanced`, Hölder ambient-vector-space expansion. -/
theorem periodicCAlpha_linear_closure (a N k : ℕ) (α : ℝ) :
    (∃ z : PeriodicCAlphaFunction a N k α, z.toFun = 0) ∧
    (∀ f g : PeriodicCAlphaFunction a N k α,
      ∃ h : PeriodicCAlphaFunction a N k α, h.toFun = f.toFun + g.toFun) ∧
    (∀ (c : ℝ) (f : PeriodicCAlphaFunction a N k α),
      ∃ h : PeriodicCAlphaFunction a N k α, h.toFun = c • f.toFun) := by
  constructor
  · refine ⟨⟨0, ?_, contDiff_const, ?_, ?_⟩, rfl⟩
    · simp
    · intro j hj
      exact ⟨0, by simp⟩
    · exact ⟨0, by simp⟩
  constructor
  · intro f g
    refine ⟨⟨f.toFun + g.toFun, ?_, f.contDiff.add g.contDiff, ?_, ?_⟩, rfl⟩
    · intro x n
      simp only [Pi.add_apply, f.periodic, g.periodic]
    · intro j hj
      obtain ⟨Cf, hf⟩ := f.derivative_bounded j hj
      obtain ⟨Cg, hg⟩ := g.derivative_bounded j hj
      refine ⟨Cf + Cg, ?_⟩
      intro x hx
      rw [iteratedFDeriv_add (f.contDiff.of_le (by exact_mod_cast hj))
        (g.contDiff.of_le (by exact_mod_cast hj)), Pi.add_apply]
      exact (norm_add_le _ _).trans (add_le_add (hf x hx) (hg x hx))
    · obtain ⟨Cf, hf⟩ := f.holder_bounded
      obtain ⟨Cg, hg⟩ := g.holder_bounded
      refine ⟨Cf + Cg, ?_⟩
      intro x y d hd
      rw [iteratedFDeriv_add f.contDiff g.contDiff]
      simp only [Pi.add_apply]
      have hh : (iteratedFDeriv ℝ k f.toFun x + iteratedFDeriv ℝ k g.toFun x) -
          (iteratedFDeriv ℝ k f.toFun y + iteratedFDeriv ℝ k g.toFun y) =
          (iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y) +
          (iteratedFDeriv ℝ k g.toFun x - iteratedFDeriv ℝ k g.toFun y) := by abel
      rw [hh]
      calc
        _ ≤ (‖iteratedFDeriv ℝ k f.toFun x - iteratedFDeriv ℝ k f.toFun y‖ +
            ‖iteratedFDeriv ℝ k g.toFun x - iteratedFDeriv ℝ k g.toFun y‖) / d ^ α :=
          div_le_div_of_nonneg_right (norm_add_le _ _) (Real.rpow_nonneg hd.le _)
        _ = _ := add_div _ _ _
        _ ≤ Cf + Cg := add_le_add (hf x y hd) (hg x y hd)
  · intro c f
    refine ⟨⟨c • f.toFun, ?_, f.contDiff.const_smul c, ?_, ?_⟩, rfl⟩
    · intro x n
      simp only [Pi.smul_apply, f.periodic]
    · intro j hj
      obtain ⟨C, hC⟩ := f.derivative_bounded j hj
      refine ⟨‖c‖ * C, ?_⟩
      intro x hx
      rw [iteratedFDeriv_const_smul_apply (f.contDiff.of_le (by exact_mod_cast hj)).contDiffAt,
        norm_smul]
      exact mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg _)
    · obtain ⟨C, hC⟩ := f.holder_bounded
      refine ⟨‖c‖ * C, ?_⟩
      intro x y d hd
      rw [iteratedFDeriv_const_smul_apply f.contDiff.contDiffAt,
        iteratedFDeriv_const_smul_apply f.contDiff.contDiffAt, ← smul_sub, norm_smul]
      rw [mul_div_assoc]
      exact mul_le_mul_of_nonneg_left (hC x y hd) (norm_nonneg _)

#print axioms periodicCAlpha_linear_closure

end GlobalEmbedding.Paper
