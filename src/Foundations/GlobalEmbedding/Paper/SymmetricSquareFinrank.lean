import GlobalEmbedding.Paper.SupportedRankSymmetricSquareSplitting
import Mathlib.RingTheory.TensorProduct.Finite
import Mathlib.LinearAlgebra.Dual.Lemmas
import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic

/-!
# Dimension of the original binary symmetric-square quotient

Source: original main.tex 948–961 and 1007–1008. Reuse the accepted exact quotient
splitting and native finite-dimensional linear algebra. No new symmetric carrier,
norm, basis, or monomial framework is introduced. DAG: `symmetric-square-finrank`.
-/

noncomputable section

open Module
open scoped TensorProduct

namespace GlobalEmbedding.Paper

universe u

/-- The dimension of the SAME binary quotient in every finite dimension, including zero.
Proof: the accepted splitting adds a mixed summand of dimension n at the nth step.
Native binomial recurrence sums these dimensions. Source: `prop:saturation`. -/
theorem symmetricSquare_finrank (V : Type u) [AddCommGroup V] [Module ℝ V]
    [FiniteDimensional ℝ V] :
    finrank ℝ (SymmetricSquare V) = finrank ℝ V * (finrank ℝ V + 1) / 2 := by
  classical
  have aux : ∀ n : ℕ, ∀ (W : Type u) [AddCommGroup W] [Module ℝ W]
      [FiniteDimensional ℝ W], finrank ℝ W = n →
        finrank ℝ (SymmetricSquare W) = (n + 1).choose 2 := by
    intro n
    induction n with
    | zero =>
      intro W _ _ _ hW
      have ht : finrank ℝ (W ⊗[ℝ] W) = 0 := by
        simp only [Module.finrank_tensorProduct, hW, zero_mul]
      have hq := Submodule.finrank_quotient_le (symmetricSquareRelations W)
      change finrank ℝ (SymmetricSquare W) ≤ finrank ℝ (W ⊗[ℝ] W) at hq
      rw [ht] at hq
      have hs : finrank ℝ (SymmetricSquare W) = 0 := Nat.eq_zero_of_le_zero hq
      simpa using hs
    | succ n ih =>
      intro W _ _ _ hW
      have : Nontrivial W := Module.nontrivial_of_finrank_pos (R := ℝ)
        (by rw [hW]; exact Nat.succ_pos n)
      obtain ⟨z, hz⟩ := exists_ne (0 : W)
      obtain ⟨f, hf⟩ := Module.Projective.exists_dual_eq_one ℝ hz
      have hf0 : f ≠ 0 := by intro h; simp [h] at hf
      have hker : finrank ℝ (LinearMap.ker f) = n := by
        have hk := Module.Dual.finrank_ker_add_one_of_ne_zero hf0
        omega
      let e : (LinearMap.ker f × ℝ) ≃ₗ[ℝ] W :=
        LinearEquiv.ofFinrankEq _ _ (by simp [Module.finrank_prod, hker, hW])
      obtain ⟨_, _, _, hm, Φ, _⟩ := supported_rank_symmetric_square_splitting e
      have hi := ih (LinearMap.ker f) hker
      have hd := Φ.finrank_eq
      rw [Module.finrank_prod, hm, hi] at hd
      rw [hW] at hd
      have hc : (n + 1 + 1).choose 2 = n + 1 + (n + 1).choose 2 := by
        simpa only [Nat.choose_one_right, Nat.succ_eq_add_one] using
          Nat.choose_succ_succ (n + 1) 1
      omega
  have h := aux (finrank ℝ V) V rfl
  simpa [Nat.choose_two_right, Nat.mul_comm] using h

/-- An onto original second-form map has kernel dimension n−1 at the required target size.
No phase or inner-product hypothesis is needed for this algebraic consequence.
The zero-dimensional impossible onto case is handled by the same rank-nullity equation.
Source: `prop:saturation`, the onto case d=n−1. -/
theorem symmetricSquare_surjective_kernel_finrank
    {V W : Type*} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    [AddCommGroup W] [Module ℝ W] [FiniteDimensional ℝ W]
    (B : SymmetricSquare V →ₗ[ℝ] W) (hB : Function.Surjective B)
    (hW : finrank ℝ W = finrank ℝ V * (finrank ℝ V - 1) / 2 + 1) :
    finrank ℝ (LinearMap.ker B) = finrank ℝ V - 1 := by
  have hr := B.finrank_range_add_finrank_ker
  rw [LinearMap.range_eq_top.mpr hB, finrank_top, symmetricSquare_finrank] at hr
  have hc : (finrank ℝ V + 1).choose 2 = finrank ℝ V + (finrank ℝ V).choose 2 := by
    simpa only [Nat.choose_one_right, Nat.succ_eq_add_one] using
      Nat.choose_succ_succ (finrank ℝ V) 1
  rw [Nat.choose_two_right, Nat.choose_two_right] at hc
  simp only [Nat.add_sub_cancel] at hc
  rw [Nat.mul_comm (finrank ℝ V + 1) (finrank ℝ V)] at hc
  omega

end GlobalEmbedding.Paper
