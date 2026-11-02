import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Complex.Basic
import Mathlib.Tactic

/-!
# The actual finite weighted product in the fast multiplier

Source: main.tex633–675, lem:increments. The native REAL derivative rule for
scalar multiplication is reused directly; the complex vector target is not
assumed to be a normed ring. W6's unwritten checkpoint interface is preserved.
This intermediate's phase-jet premise is discharged by W3's actual phase theorem
in the full multiplier; it is never a new original-target premise.
-/

noncomputable section

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The original scaled Leibniz estimate is only a weighted application of the
native scalar-multiplication derivative bound. No Leibniz rule is reproved.
Source: the weighted nonzero-mode estimate in lem:increments. -/
theorem increments_fast_smul_jet_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (O : Set E) (hO : IsOpen O) (w : E → ℂ) (z : E → F)
    (hw : ContDiffOn ℝ ∞ w O) (hz : ContDiffOn ℝ ∞ z O)
    (x : E) (hx : x ∈ O) (j n : ℕ) (hn : n ≤ j)
    (τ ℓ : ℝ) (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (A : ℕ → ℝ)
    (hphase : ∀ i ≤ j, τ ^ i * ‖iteratedFDeriv ℝ i w x‖ ≤ A i) :
    τ ^ n * ‖iteratedFDeriv ℝ n (fun y ↦ w y • z y) x‖ ≤
      ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * A i * ℓ ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) z x‖ := by
  have hnative := norm_iteratedFDerivWithin_smul_le hw hz hO.uniqueDiffOn hx
    (by simp : (n : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at hnative
  calc
    _ ≤ τ ^ n * ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * ‖iteratedFDeriv ℝ i w x‖ *
          ‖iteratedFDeriv ℝ (n - i) z x‖ :=
      mul_le_mul_of_nonneg_left hnative (pow_nonneg hτ.le _)
    _ = ∑ i ∈ Finset.range (n + 1), τ ^ n *
        ((n.choose i : ℝ) * ‖iteratedFDeriv ℝ i w x‖ *
          ‖iteratedFDeriv ℝ (n - i) z x‖) := by rw [Finset.mul_sum]
    _ ≤ _ := by
      apply Finset.sum_le_sum
      intro i hi
      have hin : i ≤ n := by simpa using hi
      have hpow : τ ^ n = τ ^ i * τ ^ (n - i) := by
        rw [← pow_add, Nat.add_sub_of_le hin]
      have hA : 0 ≤ A i :=
        (mul_nonneg (pow_nonneg hτ.le _) (norm_nonneg _)).trans (hphase i (hin.trans hn))
      calc
        _ = (n.choose i : ℝ) * (τ ^ i * ‖iteratedFDeriv ℝ i w x‖) *
            τ ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) z x‖ := by rw [hpow]; ring
        _ ≤ (n.choose i : ℝ) * A i *
            τ ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) z x‖ := by
          gcongr
          exact hphase i (hin.trans hn)
        _ ≤ _ := by
          gcongr

/-- One finite constant controls the complete weighted exact-order jet sum.
All orders use the same actual scalar and vector functions and the same scales.
Source: finite weighted product summation in lem:increments. -/
theorem increments_fast_smul_weighted_sum_bound
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [NormedSpace ℂ F]
    [IsScalarTower ℝ ℂ F]
    (O : Set E) (hO : IsOpen O) (w : E → ℂ) (z : E → F)
    (hw : ContDiffOn ℝ ∞ w O) (hz : ContDiffOn ℝ ∞ z O)
    (x : E) (hx : x ∈ O) (j : ℕ)
    (τ ℓ : ℝ) (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (A : ℕ → ℝ)
    (hphase : ∀ i ≤ j, τ ^ i * ‖iteratedFDeriv ℝ i w x‖ ≤ A i) :
    (∑ n ∈ Finset.range (j + 1),
      τ ^ n * ‖iteratedFDeriv ℝ n (fun y ↦ w y • z y) x‖) ≤
      (∑ n ∈ Finset.range (j + 1), ∑ i ∈ Finset.range (n + 1),
        (n.choose i : ℝ) * A i) *
      ∑ b ∈ Finset.range (j + 1), ℓ ^ b * ‖iteratedFDeriv ℝ b z x‖ := by
  have hℓ : 0 ≤ ℓ := hτ.le.trans hτℓ
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro n hn
  have hnj : n ≤ j := by simpa using hn
  apply (increments_fast_smul_jet_bound O hO w z hw hz x hx j n hnj
    τ ℓ hτ hτℓ A hphase).trans
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro i hi
  have hin : i ≤ n := by simpa using hi
  have hA : 0 ≤ A i :=
    (mul_nonneg (pow_nonneg hτ.le _) (norm_nonneg _)).trans (hphase i (hin.trans hnj))
  have hmem : n - i ∈ Finset.range (j + 1) :=
    Finset.mem_range.mpr (Nat.lt_succ_of_le ((Nat.sub_le n i).trans hnj))
  have hterm : ℓ ^ (n - i) * ‖iteratedFDeriv ℝ (n - i) z x‖ ≤
      ∑ b ∈ Finset.range (j + 1), ℓ ^ b * ‖iteratedFDeriv ℝ b z x‖ :=
    Finset.single_le_sum
      (f := fun b ↦ ℓ ^ b * ‖iteratedFDeriv ℝ b z x‖)
      (fun b _ ↦ mul_nonneg (pow_nonneg hℓ b) (norm_nonneg _)) hmem
  simpa only [mul_assoc] using
    mul_le_mul_of_nonneg_left hterm (mul_nonneg (Nat.cast_nonneg _) hA)

/-- The actual coordinatewise real-part map between the existing Pi spaces.
It uses the native complex real-part CLM in every coordinate, without a new norm.
Source: taking the real displacement in lem:increments. -/
def incrementsCoordinateRealPart (N : ℕ) : (Fin N → ℂ) →L[ℝ] (Fin N → ℝ) :=
  ContinuousLinearMap.pi fun i ↦ Complex.reCLM.comp (ContinuousLinearMap.proj i)

/-- Actual coordinate real part is a contraction, including the empty target. -/
theorem incrementsCoordinateRealPart_norm_le (N : ℕ) :
    ‖incrementsCoordinateRealPart N‖ ≤ 1 := by
  apply (incrementsCoordinateRealPart N).opNorm_le_bound zero_le_one
  intro z
  rw [one_mul]
  apply (pi_norm_le_iff_of_nonneg (norm_nonneg z)).mpr
  intro i
  exact (RCLike.norm_re_le_norm (z i)).trans (norm_le_pi_norm z i)

/-- Real part contracts every actual real jet on the original open domain.
This is native bounded linear postcomposition, not a formal derivative assignment. -/
theorem incrementsCoordinateRealPart_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (N a : ℕ) (O : Set E) (hO : IsOpen O) (f : E → Fin N → ℂ)
    (hf : ContDiffOn ℝ ∞ f O) (x : E) (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ a (fun y i ↦ (f y i).re) x‖ ≤
      ‖iteratedFDeriv ℝ a f x‖ := by
  have h := (incrementsCoordinateRealPart N).norm_iteratedFDerivWithin_comp_left
    (hf x hx) hO.uniqueDiffOn hx (by simp : (a : ℕ∞ω) ≤ ∞)
  simp only [iteratedFDerivWithin_of_isOpen _ hO hx] at h
  exact h.trans (mul_le_of_le_one_left (norm_nonneg _)
    (incrementsCoordinateRealPart_norm_le N))

end GlobalEmbedding.Paper
