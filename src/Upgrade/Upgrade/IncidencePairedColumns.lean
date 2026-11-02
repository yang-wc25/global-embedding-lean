import Upgrade.IncidencePerturbation
import GlobalEmbedding.Offline.PairedValueCoincidenceRank

/-!
# Actual paired columns after composing with an incidence equation

The previously proved radial-pair identity is reused.  This file handles the
new issue that a Schur or supported equation is evaluated at a moving actual
second form.  Its derivative variation and both global value remainders remain
in the estimate.  No incidence rank or localized corrected family is assumed.
-/

noncomputable section
open GlobalEmbedding.Offline

namespace GlobalEmbedding.Upgrade

variable {P X Y T R V : Type*}
  [NormedAddCommGroup P] [NormedSpace ℝ P]
  [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup T] [NormedSpace ℝ T]
  [NormedAddCommGroup R] [NormedSpace ℝ R]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

/-- Divide an actual error by its positive response scale. -/
theorem norm_rescaled_error_le (v : V) {a eps : ℝ} (ha : 0 < a)
    (hv : ‖v‖ ≤ a * eps) : ‖a⁻¹ • v‖ ≤ eps := by
  rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr ha)]
  calc
    a⁻¹ * ‖v‖ ≤ a⁻¹ * (a * eps) :=
      mul_le_mul_of_nonneg_left hv (inv_nonneg.mpr ha.le)
    _ = eps := by rw [← mul_assoc, inv_mul_cancel₀ ha.ne', one_mul]

/-- Exact error identity for the actual normalized parameter derivative.
`D₀` is the reference derivative of the chosen defining equation.  The
current derivative is the literal `fderiv equation (B u x)`.

Only the leading column vanishes at the second endpoint: `eV0y,eV1y` remain
the actual two global remainder columns of the same family. -/
theorem scaledIncidence_paired_column_error
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a theta : ℝ) (hsigma : sigma ≠ 0) (ha : a ≠ 0)
    (u : P) (x : X) (y : Y) (d0 d1 : P) (A : T) (v : V)
    (D₀ : T →L[ℝ] R) (eB0 eB1 : T) (eV0x eV0y eV1x eV1y : V)
    (hB : DifferentiableAt ℝ (fun w ↦ B w x) u)
    (hR : DifferentiableAt ℝ equation (B u x))
    (hx : DifferentiableAt ℝ (fun w ↦ F w x) u)
    (hy : DifferentiableAt ℝ (fun w ↦ H w y) u)
    (hB0 : fderiv ℝ (fun w ↦ B w x) u d0 = (sigma * Real.cos theta) • A + eB0)
    (hB1 : fderiv ℝ (fun w ↦ B w x) u d1 = (sigma * Real.sin theta) • A + eB1)
    (hV0x : fderiv ℝ (fun w ↦ F w x) u d0 = (a * Real.cos theta) • v + eV0x)
    (hV1x : fderiv ℝ (fun w ↦ F w x) u d1 = (a * Real.sin theta) • v + eV1x)
    (hV0y : fderiv ℝ (fun w ↦ H w y) u d0 = eV0y)
    (hV1y : fderiv ℝ (fun w ↦ H w y) u d1 = eV1y) :
    fderiv ℝ (fun w ↦ scaledIncidence B F H equation sigma a w x y) u
        (pairedRadialDirection theta d0 d1) - (D₀ A, v) =
      ((fderiv ℝ equation (B u x) - D₀) A +
        sigma⁻¹ • fderiv ℝ equation (B u x)
          (Real.cos theta • eB0 + Real.sin theta • eB1),
        a⁻¹ • (Real.cos theta • (eV0x - eV0y) +
          Real.sin theta • (eV1x - eV1y))) := by
  have hb := pairedRadialDirection_response (fderiv ℝ (fun w ↦ B w x) u)
    theta sigma d0 d1 A eB0 eB1 hB0 hB1
  have h0 : (fderiv ℝ (fun w ↦ F w x) u - fderiv ℝ (fun w ↦ H w y) u) d0 =
      (a * Real.cos theta) • v + (eV0x - eV0y) := by
    simp only [ContinuousLinearMap.sub_apply, hV0x, hV0y]
    abel
  have h1 : (fderiv ℝ (fun w ↦ F w x) u - fderiv ℝ (fun w ↦ H w y) u) d1 =
      (a * Real.sin theta) • v + (eV1x - eV1y) := by
    simp only [ContinuousLinearMap.sub_apply, hV1x, hV1y]
    abel
  have hv := pairedRadialDirection_response
    (fderiv ℝ (fun w ↦ F w x) u - fderiv ℝ (fun w ↦ H w y) u)
    theta a d0 d1 v (eV0x - eV0y) (eV1x - eV1y) h0 h1
  rw [(hasFDerivAt_scaledIncidence_parameter B F H equation sigma a u x y
    hB hR hx hy).fderiv]
  apply Prod.ext
  · simp only [Prod.fst_sub, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, hb,
      map_add, map_smul, smul_add, smul_smul, inv_mul_cancel₀ hsigma, one_smul,
      ContinuousLinearMap.sub_apply]
    abel
  · simp only [Prod.snd_sub, ContinuousLinearMap.prod_apply,
      ContinuousLinearMap.smul_apply, hv, smul_add, smul_smul,
      inv_mul_cancel₀ ha, one_smul]
    abel

/-- Uniform actual paired-incidence error, with the derivative variation of
the equation and all four global value errors explicitly present. The fixed
factor four reuses the already verified radial-remainder bound. -/
theorem norm_scaledIncidence_paired_error_le
    (B : P → X → T) (F : P → X → V) (H : P → Y → V) (equation : T → R)
    (sigma a theta : ℝ) (hsigma : 0 < sigma) (ha : 0 < a)
    (u : P) (x : X) (y : Y) (d0 d1 : P) (A : T) (v : V)
    (D₀ : T →L[ℝ] R) (eB0 eB1 : T) (eV0x eV0y eV1x eV1y : V)
    (epsB epsV delta : ℝ) (hepsB : 0 ≤ epsB) (hepsV : 0 ≤ epsV)
    (hB : DifferentiableAt ℝ (fun w ↦ B w x) u)
    (hR : DifferentiableAt ℝ equation (B u x))
    (hx : DifferentiableAt ℝ (fun w ↦ F w x) u)
    (hy : DifferentiableAt ℝ (fun w ↦ H w y) u)
    (hB0 : fderiv ℝ (fun w ↦ B w x) u d0 = (sigma * Real.cos theta) • A + eB0)
    (hB1 : fderiv ℝ (fun w ↦ B w x) u d1 = (sigma * Real.sin theta) • A + eB1)
    (hV0x : fderiv ℝ (fun w ↦ F w x) u d0 = (a * Real.cos theta) • v + eV0x)
    (hV1x : fderiv ℝ (fun w ↦ F w x) u d1 = (a * Real.sin theta) • v + eV1x)
    (hV0y : fderiv ℝ (fun w ↦ H w y) u d0 = eV0y)
    (hV1y : fderiv ℝ (fun w ↦ H w y) u d1 = eV1y)
    (hEB0 : ‖eB0‖ ≤ sigma * epsB) (hEB1 : ‖eB1‖ ≤ sigma * epsB)
    (hEV0x : ‖eV0x‖ ≤ a * epsV) (hEV0y : ‖eV0y‖ ≤ a * epsV)
    (hEV1x : ‖eV1x‖ ≤ a * epsV) (hEV1y : ‖eV1y‖ ≤ a * epsV)
    (hD : ‖fderiv ℝ equation (B u x) - D₀‖ ≤ delta) :
    ‖fderiv ℝ (fun w ↦ scaledIncidence B F H equation sigma a w x y) u
        (pairedRadialDirection theta d0 d1) - (D₀ A, v)‖ ≤
      max (delta * ‖A‖ + 4 * ‖fderiv ℝ equation (B u x)‖ * epsB) (4 * epsV) := by
  rw [scaledIncidence_paired_column_error B F H equation sigma a theta hsigma.ne' ha.ne'
    u x y d0 d1 A v D₀ eB0 eB1 eV0x eV0y eV1x eV1y
    hB hR hx hy hB0 hB1 hV0x hV1x hV0y hV1y]
  have hb : ‖Real.cos theta • eB0 + Real.sin theta • eB1‖ ≤ 4 * (sigma * epsB) := by
    simpa only [sub_zero] using pairedRadialDirection_four_remainders_norm_le
      theta eB0 (0 : T) eB1 (0 : T) (mul_nonneg hsigma.le hepsB)
      hEB0 (by simp; positivity) hEB1 (by simp; positivity)
  have hbr : ‖sigma⁻¹ • fderiv ℝ equation (B u x)
      (Real.cos theta • eB0 + Real.sin theta • eB1)‖ ≤
        4 * ‖fderiv ℝ equation (B u x)‖ * epsB := by
    apply norm_rescaled_error_le _ hsigma
    calc
      _ ≤ ‖fderiv ℝ equation (B u x)‖ *
          ‖Real.cos theta • eB0 + Real.sin theta • eB1‖ :=
        ContinuousLinearMap.le_opNorm _ _
      _ ≤ ‖fderiv ℝ equation (B u x)‖ * (4 * (sigma * epsB)) :=
        mul_le_mul_of_nonneg_left hb (norm_nonneg _)
      _ = _ := by ring
  have hv : ‖a⁻¹ • (Real.cos theta • (eV0x - eV0y) +
      Real.sin theta • (eV1x - eV1y))‖ ≤ 4 * epsV := by
    apply norm_rescaled_error_le _ ha
    convert pairedRadialDirection_four_remainders_norm_le theta eV0x eV0y eV1x eV1y
      (mul_nonneg ha.le hepsV) hEV0x hEV0y hEV1x hEV1y using 1 <;> ring
  apply norm_prod_le_iff.mpr
  constructor
  · exact (norm_add_le _ _).trans ((add_le_add
      ((ContinuousLinearMap.le_opNorm _ A).trans
        (mul_le_mul_of_nonneg_right hD (norm_nonneg A))) hbr).trans (le_max_left _ _))
  · exact hv.trans (le_max_right _ _)

end GlobalEmbedding.Upgrade
