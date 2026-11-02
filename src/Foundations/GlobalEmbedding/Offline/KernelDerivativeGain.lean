import GlobalEmbedding.Offline.SignedSmoothing
import Mathlib.Analysis.Calculus.ContDiff.Convolution

/-!
# Actual kernel derivatives and smoothing gain

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
and `repair-local-convolution-estimates`, derivative-gain step.

This file moves every actual Fréchet derivative onto the smooth compact
kernel. The right factor only needs local integrability. The induction
uses Mathlib's actual derivative-of-convolution theorem and the native
continuous multilinear currying maps, following the reusable pattern in
the accepted `CollarGaussianDerivativeConvolution` module, with the
compact support placed on the kernel instead of the source.
-/

open MeasureTheory
open scoped BigOperators ContDiff Convolution

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]

omit [CompleteSpace F] in
/-- The fixed-template smoothing integral is exactly convolution with
the correctly rescaled kernel, for every positive scale. -/
theorem convolution_scaledMomentKernel_eq_signedSmoothing
    (K : E → ℝ) (u : E → F) {ell : ℝ} (hell : 0 < ell) (x : E) :
    ((scaledMomentKernel ell K) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u) x =
      signedSmoothing mu K ell u x := by
  let f := fun y : E => K y • u (x - ell • y)
  have hscale : (fun y : E => scaledMomentKernel ell K y • u (x - y)) =
      fun y => (ell ^ Module.finrank ℝ E)⁻¹ • f (ell⁻¹ • y) := by
    funext y
    simp [scaledMomentKernel, f, smul_smul, hell.ne']
  rw [convolution_lsmul, hscale, integral_smul,
    Measure.integral_comp_inv_smul_of_nonneg mu f hell.le]
  simp only [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hell.ne'), one_smul]
  rfl

omit [CompleteSpace F] in
/-- Every actual derivative of convolution is convolution of the actual
kernel derivative, with the source unchanged. No support hypothesis is
made on the source. -/
theorem convolution_iteratedFDeriv_kernel {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} (hu : LocallyIntegrable u mu) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u) x =
      ∫ y, (iteratedFDeriv ℝ j K y).smulRight (u (x - y)) ∂mu := by
  let L (k : ℕ) := ContinuousMultilinearMap.smulRightL ℝ (fun _ : Fin k => E) F
  let H := K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u
  have hderiv (k : ℕ) : iteratedFDeriv ℝ k H =
      (iteratedFDeriv ℝ k K) ⋆[L k, mu] u := by
    induction k with
    | zero =>
      funext z
      let e := (continuousMultilinearCurryFin0 ℝ E F).symm.toContinuousLinearEquiv
      change e (∫ y, K y • u (z - y) ∂mu) =
        ∫ y, (iteratedFDeriv ℝ 0 K y).smulRight (u (z - y)) ∂mu
      rw [← e.integral_comp_comm (fun y => K y • u (z - y))]
      congr 1
    | succ k ih =>
      funext z
      rw [iteratedFDeriv_succ_eq_comp_left, Function.comp_apply, ih]
      have hsmooth : ContDiff ℝ 1 (iteratedFDeriv ℝ k K) :=
        hK.iteratedFDeriv_right (by simp)
      have hd := (hKcompact.iteratedFDeriv k).hasFDerivAt_convolution_left
        (L k) hsmooth hu z
      rw [hd.fderiv]
      let e := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (k + 1) => E) F).symm
        |>.toContinuousLinearEquiv
      change e (∫ y, (L k).precompL E (fderiv ℝ (iteratedFDeriv ℝ k K) y)
          (u (z - y)) ∂mu) =
        ∫ y, (iteratedFDeriv ℝ (k + 1) K y).smulRight (u (z - y)) ∂mu
      rw [← e.integral_comp_comm (fun y : E =>
        (L k).precompL E (fderiv ℝ (iteratedFDeriv ℝ k K) y) (u (z - y)))]
      congr 1
  change iteratedFDeriv ℝ j H x = _
  rw [hderiv j]
  rfl

omit [CompleteSpace F] in
/-- A local C0 bound on the source over the translated kernel support
controls every actual derivative of its convolution by the derivative's
true L1 norm. No global compact-support assumption is made on the source. -/
theorem convolution_iteratedFDeriv_norm_le {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} (hu : LocallyIntegrable u mu) (j : ℕ) (x : E) (B : ℝ)
    (hB : ∀ y ∈ tsupport K, ‖u (x - y)‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (K ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u) x‖ ≤
      B * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  rw [convolution_iteratedFDeriv_kernel mu hK hKcompact hu]
  have hcont : Continuous (iteratedFDeriv ℝ j K) :=
    ContDiff.continuous_iteratedFDeriv (by simp) hK
  have hInt : Integrable (fun y => ‖iteratedFDeriv ℝ j K y‖ * B) mu :=
    (hcont.integrable_of_hasCompactSupport (hKcompact.iteratedFDeriv j)).norm.mul_const B
  calc
    ‖∫ y, (iteratedFDeriv ℝ j K y).smulRight (u (x - y)) ∂mu‖ ≤
        ∫ y, ‖iteratedFDeriv ℝ j K y‖ * B ∂mu := by
      apply norm_integral_le_of_norm_le hInt
      filter_upwards [] with y
      rw [ContinuousMultilinearMap.norm_smulRight]
      by_cases hy : iteratedFDeriv ℝ j K y = 0
      · simp [hy]
      · exact mul_le_mul_of_nonneg_left
          (hB y (support_iteratedFDeriv_subset j hy)) (norm_nonneg _)
    _ = B * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
      rw [integral_mul_const, mul_comm]

omit [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Differentiating the actual rescaled kernel produces exactly one
factor of the inverse scale for each derivative, in addition to the
Jacobian normalization. -/
theorem scaledMomentKernel_iteratedFDeriv {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (ell : ℝ) (j : ℕ) (x : E) :
    iteratedFDeriv ℝ j (scaledMomentKernel ell K) x =
      ((ell ^ Module.finrank ℝ E)⁻¹ * (ell⁻¹)^j) •
        iteratedFDeriv ℝ j K (ell⁻¹ • x) := by
  have hcomp : ContDiff ℝ j (fun y : E => K (ell⁻¹ • y)) :=
    (hK.of_le (by simp)).comp (contDiff_const.smul contDiff_id)
  change iteratedFDeriv ℝ j
    (fun y => (ell ^ Module.finrank ℝ E)⁻¹ • K (ell⁻¹ • y)) x = _
  rw [iteratedFDeriv_const_smul_apply' hcomp.contDiffAt,
    iteratedFDeriv_comp_const_smul _ (hK.of_le (by simp))]
  simp only [smul_smul]

/-- The L1 norm of the j-th rescaled derivative is the fixed template
L1 norm times exactly ell to the power minus j. The ambient dimension
cancels against the Haar Jacobian. -/
theorem scaledMomentKernel_derivative_L1 {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) {ell : ℝ} (hell : 0 < ell) (j : ℕ) :
    (∫ y, ‖iteratedFDeriv ℝ j (scaledMomentKernel ell K) y‖ ∂mu) =
      (ell⁻¹)^j * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  simp_rw [scaledMomentKernel_iteratedFDeriv hK, norm_smul,
    Real.norm_eq_abs, abs_of_nonneg
      (mul_nonneg (inv_nonneg.mpr (pow_nonneg hell.le _))
        (pow_nonneg (inv_nonneg.mpr hell.le) _))]
  rw [integral_const_mul,
    Measure.integral_comp_inv_smul_of_nonneg mu
      (fun y => ‖iteratedFDeriv ℝ j K y‖) hell.le]
  rw [smul_eq_mul]
  field_simp

omit [CompleteSpace F] in
/-- The actual smoothing operator has the full derivative gain at every
positive scale. The bound is local to the scaled kernel support and its
constant is an actual fixed-template derivative L1 norm. -/
theorem signedSmoothing_iteratedFDeriv_norm_le {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} (hu : LocallyIntegrable u mu) {ell : ℝ} (hell : 0 < ell)
    (j : ℕ) (x : E) (B : ℝ)
    (hB : ∀ y ∈ tsupport (scaledMomentKernel ell K), ‖u (x - y)‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (signedSmoothing mu K ell u) x‖ ≤
      B * (ell⁻¹)^j * ∫ y, ‖iteratedFDeriv ℝ j K y‖ ∂mu := by
  have heq : signedSmoothing mu K ell u =
      (scaledMomentKernel ell K) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u := by
    funext z
    exact (convolution_scaledMomentKernel_eq_signedSmoothing mu K u hell z).symm
  rw [heq]
  have h := convolution_iteratedFDeriv_norm_le mu
    (scaledMomentKernel_contDiff hK ell)
    (scaledMomentKernel_hasCompactSupport hKcompact hell.ne') hu j x B hB
  rw [scaledMomentKernel_derivative_L1 mu hK hell j] at h
  simpa only [mul_assoc] using h

omit [CompleteSpace F] in
/-- The source may be merely locally integrable: smoothing by the actual
smooth compact kernel yields an actual globally smooth function. -/
theorem signedSmoothing_contDiff {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} (hu : LocallyIntegrable u mu) {ell : ℝ} (hell : 0 < ell) :
    ContDiff ℝ ∞ (signedSmoothing mu K ell u) := by
  have heq : signedSmoothing mu K ell u =
      (scaledMomentKernel ell K) ⋆[ContinuousLinearMap.lsmul ℝ ℝ, mu] u := by
    funext z
    exact (convolution_scaledMomentKernel_eq_signedSmoothing mu K u hell z).symm
  rw [heq]
  exact (scaledMomentKernel_hasCompactSupport hKcompact hell.ne').contDiff_convolution_left
    (ContinuousLinearMap.lsmul ℝ ℝ) (scaledMomentKernel_contDiff hK ell) hu

end

end GlobalEmbedding.Offline
