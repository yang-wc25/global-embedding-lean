import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.Analysis.SpecialFunctions.Complex.Analytic
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Analytic real translations of genuine finite Fourier kernels

Source: `main.tex`, `lem:planar`, line261.
DAG node: `planar-fourier-orbit-analytic`.
-/

noncomputable section

open Set MeasureTheory Topology

namespace GlobalEmbedding.Paper

/-- Translate an actual continuous circle kernel by a real time. -/
def planarFourierKernelTranslate (p : C(AddCircle (1 : ℝ), ℂ)) (s : ℝ) :
    C(AddCircle (1 : ℝ), ℂ) :=
  p.comp ⟨fun t ↦ t - (s : AddCircle (1 : ℝ)), continuous_id.sub continuous_const⟩

/-- Real translation of a finite complex Fourier polynomial is analytic in the actual
continuous-map sup norm. Characters translate by the scalar complex exponential; analyticity
is preserved under the actual finite linear combinations. No analytic kernel input is assumed.
Source: `lem:planar`, finite orbit Fourier approximation, line261. -/
theorem planar_fourier_kernel_translate_analytic
    (p : C(AddCircle (1 : ℝ), ℂ))
    (hp : p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ))))) :
    ∀ s : ℝ, AnalyticAt ℝ (planarFourierKernelTranslate p) s := by
  induction hp using Submodule.span_induction with
  | mem q hq =>
    obtain ⟨n, rfl⟩ := hq
    have heq : planarFourierKernelTranslate (fourier (T := (1 : ℝ)) n) =
        fun s : ℝ ↦ fourier (-n) (s : AddCircle (1 : ℝ)) • fourier n := by
      funext s
      ext t
      simp [planarFourierKernelTranslate, fourier_apply, sub_eq_add_neg,
        AddCircle.toCircle_add, AddCircle.toCircle_neg, mul_comm]
    rw [heq]
    intro s
    have ha : AnalyticAt ℝ (fun t : ℝ ↦ fourier (T := (1 : ℝ)) (-n)
        (t : AddCircle (1 : ℝ))) s := by
      simp_rw [fourier_coe_apply]
      have hc : AnalyticAt ℂ (fun z : ℂ ↦ Complex.exp (2 * Real.pi * Complex.I * (-n) * z))
          (s : ℂ) := (analyticAt_const.mul analyticAt_id).cexp
      simpa only [Function.comp_def, Int.cast_neg, Complex.ofReal_one, div_one] using
        hc.restrictScalars.comp (Complex.ofRealCLM.analyticAt s)
    exact ha.smul analyticAt_const
  | zero =>
    intro s
    have heq : planarFourierKernelTranslate 0 =
        fun _ : ℝ ↦ (0 : C(AddCircle (1 : ℝ), ℂ)) := by
      funext t; ext z; rfl
    rw [heq]
    exact analyticAt_const
  | add q r hq hr ihq ihr =>
    intro s
    have heq : planarFourierKernelTranslate (q + r) =
        planarFourierKernelTranslate q + planarFourierKernelTranslate r := by
      funext t; ext z; rfl
    rw [heq]
    exact (ihq s).add (ihr s)
  | smul c q hq ih =>
    intro s
    have heq : planarFourierKernelTranslate (c • q) =
        c • planarFourierKernelTranslate q := by
      funext t; ext z; rfl
    rw [heq]
    exact (ih s).const_smul

/-- The actual integral of the real kernel part against F is a bounded real linear map.
Its bound is the actual compact sup norm of F, by probability Haar integration.
Source: the finite-kernel orbit approximation in `lem:planar`, line261. -/
def planarFourierKernelIntegral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : C(AddCircle (1 : ℝ), E)) : C(AddCircle (1 : ℝ), ℂ) →L[ℝ] E := by
  let μ : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle
  have hint (p : C(AddCircle (1 : ℝ), ℂ)) : Integrable (fun t ↦ (p t).re • F t) μ :=
    ((Complex.continuous_re.comp p.continuous).smul F.continuous)
      |>.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  let L : C(AddCircle (1 : ℝ), ℂ) →ₗ[ℝ] E :=
    { toFun := fun p ↦ ∫ t, (p t).re • F t ∂μ
      map_add' := by
        intro p q
        simp only [ContinuousMap.add_apply, Complex.add_re, add_smul]
        exact integral_add (hint p) (hint q)
      map_smul' := by
        intro c p
        simp only [ContinuousMap.smul_apply, Complex.real_smul, Complex.mul_re,
          Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero, mul_smul]
        exact integral_smul c _ }
  refine L.mkContinuous ‖F‖ ?_
  intro p
  change ‖∫ t, (p t).re • F t ∂μ‖ ≤ ‖F‖ * ‖p‖
  have hb : ∀ t, ‖(p t).re • F t‖ ≤ ‖p‖ * ‖F‖ := by
    intro t
    rw [norm_smul, Real.norm_eq_abs]
    exact mul_le_mul ((Complex.abs_re_le_norm _).trans (p.norm_coe_le_norm t))
      (F.norm_coe_le_norm t) (norm_nonneg _) (norm_nonneg _)
  simpa [μ, mul_comm] using
    norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)

/-- A genuine finite Fourier translated-kernel integral is real analytic on every real orbit
parameter, even for arbitrary Banach-valued continuous observations. Compose the actual bounded
real linear integral map with the proved sup-norm analytic kernel translation.
Source: `lem:planar`, orbit-analytic finite Fourier approximation, line261. -/
theorem planar_fourier_translated_kernel_analytic
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : C(AddCircle (1 : ℝ), E)) (p : C(AddCircle (1 : ℝ), ℂ))
    (hp : p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ))))) :
    AnalyticOnNhd ℝ
      (fun s : ℝ ↦ ∫ t, (p (t - (s : AddCircle (1 : ℝ)))).re • F t
        ∂AddCircle.haarAddCircle) univ := by
  intro s _
  exact (planarFourierKernelIntegral F).analyticAt _ |>.comp
    (planar_fourier_kernel_translate_analytic p hp s)

#print axioms planar_fourier_kernel_translate_analytic
#print axioms planarFourierKernelIntegral
#print axioms planar_fourier_translated_kernel_analytic

end GlobalEmbedding.Paper
