import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.RestrictScalars
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Tactic

/-!
# Actual real jets of the original fast phase

Source: main.tex633–675, lem:increments. DAG: increments-fast-phase-jet-bound.
The only phase assumptions concern positive-order derivatives. The source is an
original open chart, with no analytic strengthening or global smooth extension.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- Restrict the actual complex exponential jets to REAL scalars before taking
their norm on the imaginary axis. No real-domain substitution into a complex
iterated scalar derivative theorem is used.
Source: the unit fast exponential in lem:increments. -/
theorem increments_phase_exp_real_jet_norm (r : ℝ) (a : ℕ) :
    ‖iteratedFDeriv ℝ a Complex.exp (Complex.I * (r : ℂ))‖ = 1 := by
  have hc : ContDiffAt ℂ a Complex.exp (Complex.I * (r : ℂ)) :=
    Complex.contDiff_exp.contDiffAt
  rw [← hc.restrictScalars_iteratedFDeriv (𝕜 := ℝ)]
  change ‖(iteratedFDeriv ℂ a Complex.exp (Complex.I * (r : ℂ))).restrictScalars ℝ‖ = 1
  rw [ContinuousMultilinearMap.norm_restrictScalars, norm_iteratedFDeriv_eq_norm_iteratedDeriv]
  have h := congrArg (fun f : ℂ → ℂ ↦ ‖f (Complex.I * (r : ℂ))‖)
    (iteratedDeriv_cexp_const_mul a (1 : ℂ))
  simpa only [one_mul, one_pow, Complex.norm_exp_I_mul_ofReal] using h

/-- Every requested real Frechet derivative of the literal original fast phase
has its factorial scaled bound. Only the positive-order slow phase jets enter;
in particular j=0 needs no bound on the value of psi.

The inner map is the actual real continuous linear embedding times I/tau. Its
i-th jet is bounded by (K/tau)^i using tau<=ell, K=max(1,|M|), and only i>=1.
The existing real within-composition theorem, with outer constant1 and these
inner bounds, gives a! (K/tau)^a. Multiplication by tau^a cancels the denominator.
All differentiation is local on the original open set. A separate SUP domain
S subset O is handled by applying this same pointwise theorem on S.
Source: lem:increments, finite weighted oscillatory-mode estimate, lines633–675. -/
theorem increments_fast_phase_jet_bound
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (O : Set E) (hO : IsOpen O) (ψ : E → ℝ) (hψ : ContDiffOn ℝ ∞ ψ O)
    (x : E) (hx : x ∈ O) (j : ℕ) (τ ℓ M : ℝ)
    (hτ : 0 < τ) (hτℓ : τ ≤ ℓ) (_hℓ : ℓ ≤ 1)
    (hjet : ∀ k < j, ℓ ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M) :
    ∀ a ≤ j, τ ^ a * ‖iteratedFDeriv ℝ a
      (fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ))) x‖ ≤
        (a.factorial : ℝ) * (max 1 |M|) ^ a := by
  let K := max 1 |M|
  have hK : 1 ≤ K := le_max_left _ _
  have hK0 : 0 ≤ K := zero_le_one.trans hK
  have hMK : M ≤ K := (le_abs_self M).trans (le_max_right _ _)
  let L : ℝ →L[ℝ] ℂ := (Complex.I / (τ : ℂ)) • Complex.ofRealCLM
  let φ : E → ℂ := L ∘ ψ
  have hφ : ContDiffOn ℝ ∞ φ O := L.contDiff.comp_contDiffOn hψ
  have hnormL : ‖L‖ = 1 / τ := by
    simp [L, Complex.ofRealCLM, norm_smul, abs_of_pos hτ]
  have hφeq (y : E) : φ y = Complex.I * ((ψ y / τ : ℝ) : ℂ) := by
    simp only [φ, L, Function.comp_apply, smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_div]
    ring
  intro a ha
  have houter (i : ℕ) (_hi : i ≤ a) :
      ‖iteratedFDerivWithin ℝ i Complex.exp univ (φ x)‖ ≤ (1 : ℝ) := by
    rw [iteratedFDerivWithin_univ, hφeq, increments_phase_exp_real_jet_norm]
  have hinner (i : ℕ) (hi : 1 ≤ i) (hia : i ≤ a) :
      ‖iteratedFDerivWithin ℝ i φ O x‖ ≤ (K / τ) ^ i := by
    have hd : ‖iteratedFDerivWithin ℝ i φ O x‖ ≤
        (1 / τ) * ‖iteratedFDerivWithin ℝ i ψ O x‖ := by
      simpa only [φ, hnormL] using L.norm_iteratedFDerivWithin_comp_left
        (hψ x hx) hO.uniqueDiffOn hx (by simp : (i : ℕ∞ω) ≤ ∞)
    have hj := hjet (i - 1) (by omega)
    rw [Nat.sub_add_cancel hi] at hj
    have hpow : τ ^ i = τ ^ (i - 1) * τ := by
      rw [← pow_succ, Nat.sub_add_cancel hi]
    have hcancel : τ * (1 / τ) = 1 := by field_simp
    have hpowcancel : τ ^ i * (1 / τ) = τ ^ (i - 1) := by
      rw [hpow, mul_assoc, hcancel, mul_one]
    have hb : τ ^ i * ‖iteratedFDerivWithin ℝ i φ O x‖ ≤ M := by
      calc
        _ ≤ τ ^ i * ((1 / τ) * ‖iteratedFDerivWithin ℝ i ψ O x‖) :=
          mul_le_mul_of_nonneg_left hd (pow_nonneg hτ.le _)
        _ = τ ^ (i - 1) * ‖iteratedFDeriv ℝ i ψ x‖ := by
          rw [← mul_assoc, hpowcancel, iteratedFDerivWithin_of_isOpen i hO hx]
        _ ≤ ℓ ^ (i - 1) * ‖iteratedFDeriv ℝ i ψ x‖ :=
          mul_le_mul_of_nonneg_right (pow_le_pow_left₀ hτ.le hτℓ _) (norm_nonneg _)
        _ ≤ M := hj
    have hKi : K ≤ K ^ i := by
      calc
        K = 1 * K := by ring
        _ ≤ K ^ (i - 1) * K := mul_le_mul_of_nonneg_right (one_le_pow₀ hK) hK0
        _ = K ^ i := by rw [← pow_succ, Nat.sub_add_cancel hi]
    rw [div_pow]
    apply (le_div_iff₀ (pow_pos hτ i)).mpr
    simpa only [mul_comm] using (hb.trans hMK).trans hKi
  have hc := norm_iteratedFDerivWithin_comp_le
    (𝕜 := ℝ) (n := a) (s := O) (t := univ)
    (Complex.contDiff_exp : ContDiff ℝ ∞ Complex.exp).contDiffOn hφ
    (by simp : (a : ℕ∞ω) ≤ ∞) uniqueDiffOn_univ hO.uniqueDiffOn
    (by intro y hy; trivial) hx houter hinner
  rw [iteratedFDerivWithin_of_isOpen a hO hx] at hc
  have hw : Complex.exp ∘ φ =
      fun y ↦ Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) :=
    funext (fun y ↦ congrArg Complex.exp (hφeq y))
  rw [hw, mul_one] at hc
  calc
    _ ≤ τ ^ a * ((a.factorial : ℝ) * (K / τ) ^ a) :=
      mul_le_mul_of_nonneg_left hc (pow_nonneg hτ.le _)
    _ = (a.factorial : ℝ) * ((K / τ) ^ a * τ ^ a) := by ring
    _ = (a.factorial : ℝ) * K ^ a := by rw [← mul_pow, div_mul_cancel₀ _ hτ.ne']

end GlobalEmbedding.Paper
