import Probes.ActualScaledProbe
import GlobalEmbedding.Paper.IncrementsFastMultiplier

/-!
# Original open-chart higher-derivative bounds for the actual paired columns

Source: the spatial C3 assertion after (8.4). Reuse the original finite
fast multiplier and its actual complex/real coordinate maps. No global
extension of the phase or amplitude is required: every input is on the
original open chart, with a separate evaluation point.
-/
noncomputable section
open Set GlobalEmbedding.Paper
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {N : ℕ}

/-- The original actual complex multiplier specializes to a literal cosine
wave in the native real Pi norm. -/
theorem probe_cos_fast_jet_bound
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (ψ : E → ℝ) (A : E → Fin N → ℝ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hA : ContDiffOn ℝ ∞ A O)
    (x : E) (hx : x ∈ O) (τ ell M K : ℝ)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < j, ell ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M)
    (hamp : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n (fun y ↦ Real.cos (ψ y / τ) • A y) x‖ ≤
      incrementsFastMultiplierConstant j M * K := by
  let z : E → Fin N → ℂ := fun y i ↦ (A y i : ℂ) + Complex.I * ((0 : Fin N → ℝ) i : ℂ)
  have hz : ContDiffOn ℝ ∞ z O :=
    increments_coordinate_complex_contDiffOn N O A (fun _ ↦ 0) hA contDiffOn_const
  have hzjet : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k z x‖ ≤ K := by
    intro k hk
    have h := increments_coordinate_complex_jet_bound N k O hO A (fun _ ↦ 0)
      hA contDiffOn_const x hx
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, add_zero] at h
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg (hτ.le.trans hτell) k)).trans (hamp k hk)
  have h := increments_fast_multiplier_real_jet_bound N j n hn O hO ψ z hψ hz x hx
    τ ell M K hτ hτell hell hK hphase hzjet
  have heq : (fun y i ↦ (Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) * z y i).re) =
      fun y ↦ Real.cos (ψ y / τ) • A y := by
    funext y i
    simp only [z, Pi.zero_apply, Complex.ofReal_zero, mul_zero, add_zero,
      Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, sub_zero, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_re]
  rw [heq] at h
  exact h

/-- The sine partner is the real part with pure imaginary negative amplitude;
its true native jets have the same bound. -/
theorem probe_sin_fast_jet_bound
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (ψ : E → ℝ) (A : E → Fin N → ℝ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hA : ContDiffOn ℝ ∞ A O)
    (x : E) (hx : x ∈ O) (τ ell M K : ℝ)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < j, ell ^ k * ‖iteratedFDeriv ℝ (k + 1) ψ x‖ ≤ M)
    (hamp : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n (fun y ↦ Real.sin (ψ y / τ) • A y) x‖ ≤
      incrementsFastMultiplierConstant j M * K := by
  let z : E → Fin N → ℂ := fun y i ↦ ((0 : Fin N → ℝ) i : ℂ) + Complex.I * ((-A y i : ℝ) : ℂ)
  have hz : ContDiffOn ℝ ∞ z O :=
    increments_coordinate_complex_contDiffOn N O (fun _ ↦ 0) (-A) contDiffOn_const hA.neg
  have hzjet : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k z x‖ ≤ K := by
    intro k hk
    have h := increments_coordinate_complex_jet_bound N k O hO (fun _ ↦ 0) (-A)
      contDiffOn_const hA.neg x hx
    simp only [iteratedFDeriv_fun_zero, Pi.zero_apply, norm_zero, zero_add,
      iteratedFDeriv_neg_apply, norm_neg] at h
    exact (mul_le_mul_of_nonneg_left h (pow_nonneg (hτ.le.trans hτell) k)).trans (hamp k hk)
  have h := increments_fast_multiplier_real_jet_bound N j n hn O hO ψ z hψ hz x hx
    τ ell M K hτ hτell hell hK hphase hzjet
  have heq : (fun y i ↦ (Complex.exp (Complex.I * ((ψ y / τ : ℝ) : ℂ)) * z y i).re) =
      fun y ↦ Real.sin (ψ y / τ) • A y := by
    funext y i
    simp only [z, Pi.zero_apply, Complex.ofReal_zero, zero_add,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im,
      Complex.I_re, Complex.I_im, mul_zero, zero_mul, sub_zero, one_mul,
      zero_add, Pi.smul_apply, smul_eq_mul]
    rw [mul_comm Complex.I, Complex.exp_ofReal_mul_I_im]
    ring
  rw [heq] at h
  exact h

/-- Original all-order weighted bound for the exact scaled cosine column.
The phase reference bound is on the actual fixed weighted phase `lam * ψ`. -/
theorem actualProbeCosColumn_weighted_jet_bound
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (ψ : E → ℝ) (A : E → Fin N → ℝ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hA : ContDiffOn ℝ ∞ A O)
    (x : E) (hx : x ∈ O) (δ τ ell lam M K : ℝ)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < j, ell ^ k * ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ lam * ψ y) x‖ ≤ M)
    (hamp : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n (actualProbeCosColumn δ τ lam ψ A) x‖ ≤
      |δ * τ / lam ^ 2| * (incrementsFastMultiplierConstant j M * K) := by
  have hΦ : ContDiffOn ℝ ∞ (fun y ↦ lam * ψ y) O := hψ.const_smul lam
  have h := probe_cos_fast_jet_bound j n hn O hO _ A hΦ hA x hx
    τ ell M K hτ hτell hell hK hphase hamp
  have hmod : ContDiffOn ℝ ∞ (fun y ↦ Real.cos (lam * ψ y / τ) • A y) O :=
    (hΦ.div_const τ).cos.smul hA
  have heq : actualProbeCosColumn δ τ lam ψ A =
      fun y ↦ (-(δ * τ / lam ^ 2)) • (Real.cos (lam * ψ y / τ) • A y) := by
    funext y
    rw [actualProbeCosColumn, probeFastPhase_eq]
  rw [heq, iteratedFDeriv_const_smul_apply'
    ((hmod.contDiffAt (hO.mem_nhds hx)).of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_neg]
  calc
    _ = |δ * τ / lam ^ 2| *
        (τ ^ n * ‖iteratedFDeriv ℝ n (fun y ↦ Real.cos (lam * ψ y / τ) • A y) x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The identical weighted estimate for the same scaled sine column. -/
theorem actualProbeSinColumn_weighted_jet_bound
    (j n : ℕ) (hn : n ≤ j) (O : Set E) (hO : IsOpen O)
    (ψ : E → ℝ) (A : E → Fin N → ℝ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hA : ContDiffOn ℝ ∞ A O)
    (x : E) (hx : x ∈ O) (δ τ ell lam M K : ℝ)
    (hτ : 0 < τ) (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < j, ell ^ k * ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ lam * ψ y) x‖ ≤ M)
    (hamp : ∀ k ≤ j, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ K) :
    τ ^ n * ‖iteratedFDeriv ℝ n (actualProbeSinColumn δ τ lam ψ A) x‖ ≤
      |δ * τ / lam ^ 2| * (incrementsFastMultiplierConstant j M * K) := by
  have hΦ : ContDiffOn ℝ ∞ (fun y ↦ lam * ψ y) O := hψ.const_smul lam
  have h := probe_sin_fast_jet_bound j n hn O hO _ A hΦ hA x hx
    τ ell M K hτ hτell hell hK hphase hamp
  have hmod : ContDiffOn ℝ ∞ (fun y ↦ Real.sin (lam * ψ y / τ) • A y) O :=
    (hΦ.div_const τ).sin.smul hA
  have heq : actualProbeSinColumn δ τ lam ψ A =
      fun y ↦ (-(δ * τ / lam ^ 2)) • (Real.sin (lam * ψ y / τ) • A y) := by
    funext y
    rw [actualProbeSinColumn, probeFastPhase_eq]
  rw [heq, iteratedFDeriv_const_smul_apply'
    ((hmod.contDiffAt (hO.mem_nhds hx)).of_le (by simp)), norm_smul,
    Real.norm_eq_abs, abs_neg]
  calc
    _ = |δ * τ / lam ^ 2| *
        (τ ^ n * ‖iteratedFDeriv ℝ n (fun y ↦ Real.sin (lam * ψ y / τ) • A y) x‖) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left h (abs_nonneg _)

/-- The original third-order size `δ / τ²`, including its uniform constant. -/
theorem actualProbeCosColumn_third_jet_bound
    (O : Set E) (hO : IsOpen O) (ψ : E → ℝ) (A : E → Fin N → ℝ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hA : ContDiffOn ℝ ∞ A O)
    (x : E) (hx : x ∈ O) (δ τ ell lam M K : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam)
    (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < 3, ell ^ k * ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ lam * ψ y) x‖ ≤ M)
    (hamp : ∀ k ≤ 3, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ K) :
    ‖iteratedFDeriv ℝ 3 (actualProbeCosColumn δ τ lam ψ A) x‖ ≤
      (incrementsFastMultiplierConstant 3 M * K / lam ^ 2) * (δ / τ ^ 2) := by
  have h := actualProbeCosColumn_weighted_jet_bound 3 3 le_rfl O hO ψ A hψ hA x hx
    δ τ ell lam M K hτ hτell hell hK hphase hamp
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _))] at h
  apply (mul_le_mul_iff_right₀ (pow_pos hτ 3)).mp
  apply h.trans_eq
  field_simp

/-- The paired sine third-order size uses exactly the same constant. -/
theorem actualProbeSinColumn_third_jet_bound
    (O : Set E) (hO : IsOpen O) (ψ : E → ℝ) (A : E → Fin N → ℝ)
    (hψ : ContDiffOn ℝ ∞ ψ O) (hA : ContDiffOn ℝ ∞ A O)
    (x : E) (hx : x ∈ O) (δ τ ell lam M K : ℝ)
    (hδ : 0 ≤ δ) (hτ : 0 < τ) (hlam : 0 < lam)
    (hτell : τ ≤ ell) (hell : ell ≤ 1) (hK : 0 ≤ K)
    (hphase : ∀ k < 3, ell ^ k * ‖iteratedFDeriv ℝ (k + 1) (fun y ↦ lam * ψ y) x‖ ≤ M)
    (hamp : ∀ k ≤ 3, ell ^ k * ‖iteratedFDeriv ℝ k A x‖ ≤ K) :
    ‖iteratedFDeriv ℝ 3 (actualProbeSinColumn δ τ lam ψ A) x‖ ≤
      (incrementsFastMultiplierConstant 3 M * K / lam ^ 2) * (δ / τ ^ 2) := by
  have h := actualProbeSinColumn_weighted_jet_bound 3 3 le_rfl O hO ψ A hψ hA x hx
    δ τ ell lam M K hτ hτell hell hK hphase hamp
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _))] at h
  apply (mul_le_mul_iff_right₀ (pow_pos hτ 3)).mp
  apply h.trans_eq
  field_simp

#print axioms actualProbeCosColumn_weighted_jet_bound
#print axioms actualProbeSinColumn_weighted_jet_bound
#print axioms actualProbeCosColumn_third_jet_bound
#print axioms actualProbeSinColumn_third_jet_bound
end GlobalEmbedding.Offline
