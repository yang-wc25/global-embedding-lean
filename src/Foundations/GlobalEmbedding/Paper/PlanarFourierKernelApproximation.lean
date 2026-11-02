import Mathlib.Analysis.Fourier.AddCircle
import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap

/-!
# Genuine finite Fourier kernels approximate evaluation

Source: `main.tex`, `lem:planar`, finite orbit Fourier approximation, line262.
DAG node: `planar-fourier-kernel-approximation`.
-/

open Set MeasureTheory Topology

namespace GlobalEmbedding.Paper

/-- A finite Fourier kernel approximates evaluation for an arbitrary continuous Banach-valued
circle function. Choose a nonnegative local tent and normalize by its positive Haar integral.
Continuity controls its average near zero. Fourier span density uniformly approximates this
actual scalar tent, and the compact sup norm controls the resulting Bochner integral error.
This constructs the finite kernel; neither a kernel nor an approximation estimate is assumed.
Source: `lem:planar`, finite orbit Fourier approximation, line262. -/
theorem planar_fourier_kernel_approximation
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    (F : C(AddCircle (1 : ℝ), E)) (ε : ℝ) (hε : 0 < ε) :
    ∃ p : C(AddCircle (1 : ℝ), ℂ),
      p ∈ Submodule.span ℂ (range (fourier (T := (1 : ℝ)))) ∧
      ‖(∫ t, (p t).re • F t ∂AddCircle.haarAddCircle) - F 0‖ < ε := by
  let μ : Measure (AddCircle (1 : ℝ)) := AddCircle.haarAddCircle
  have hint (f : C(AddCircle (1 : ℝ), E)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  have hintR (f : C(AddCircle (1 : ℝ), ℝ)) : Integrable f μ :=
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)
  obtain ⟨δ, hδ, hnear⟩ := Metric.continuousAt_iff.mp (F.continuous.continuousAt (x := 0))
    (ε / 4) (by positivity)
  let h₀ : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨fun t ↦ max (δ - dist t 0) 0,
      (continuous_const.sub (continuous_id.dist continuous_const)).max continuous_const⟩
  have hh₀ : ∀ t, 0 ≤ h₀ t := fun t ↦ le_max_right _ _
  have hmass : 0 < ∫ t, h₀ t ∂μ :=
    integral_pos_of_integrable_nonneg_nonzero h₀.continuous (hintR h₀) hh₀
      (x := 0) (by simpa [h₀, max_eq_left hδ.le] using hδ.ne')
  let h : C(AddCircle (1 : ℝ), ℝ) :=
    ⟨fun t ↦ h₀ t / (∫ t, h₀ t ∂μ), h₀.continuous.div_const _⟩
  have hh : ∀ t, 0 ≤ h t := fun t ↦ div_nonneg (hh₀ t) hmass.le
  have hunit : ∫ t, h t ∂μ = 1 := by
    change (∫ t, h₀ t / (∫ s, h₀ s ∂μ) ∂μ) = 1
    rw [integral_div]
    exact div_self hmass.ne'
  have hlocal : ∀ t, ‖h t • (F t - F 0)‖ ≤ h t * (ε / 4) := by
    intro t
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (hh t)]
    by_cases ht : dist t 0 < δ
    · exact mul_le_mul_of_nonneg_left
        (le_of_lt (by simpa only [dist_eq_norm] using hnear ht)) (hh t)
    · have hz : h t = 0 := by
        change max (δ - dist t 0) 0 / _ = 0
        rw [max_eq_right (sub_nonpos.mpr (le_of_not_gt ht)), zero_div]
      simp only [hz, zero_mul, le_refl]
  have havg : ‖(∫ t, h t • F t ∂μ) - F 0‖ ≤ ε / 4 := by
    have heq : (∫ t, h t • F t ∂μ) - F 0 = ∫ t, h t • (F t - F 0) ∂μ := by
      have hi₁ : Integrable (fun t ↦ h t • F t) μ :=
        hint ⟨_, h.continuous.smul F.continuous⟩
      have hi₂ : Integrable (fun t ↦ h t • F 0) μ :=
        hint ⟨_, h.continuous.smul continuous_const⟩
      simp_rw [smul_sub]
      rw [integral_sub hi₁ hi₂, integral_smul_const, hunit, one_smul]
    rw [heq]
    calc
      _ ≤ ∫ t, h t * (ε / 4) ∂μ := norm_integral_le_of_norm_le
        ((hintR h).mul_const _) (Filter.Eventually.of_forall hlocal)
      _ = ε / 4 := by rw [integral_mul_const, hunit, one_mul]
  let hc : C(AddCircle (1 : ℝ), ℂ) :=
    ⟨fun t ↦ (h t : ℂ), Complex.continuous_ofReal.comp h.continuous⟩
  have hdense : hc ∈ closure
      (Submodule.span ℂ (range (fourier (T := (1 : ℝ)))) :
        Set C(AddCircle (1 : ℝ), ℂ)) := by
    rw [← Submodule.topologicalClosure_coe, span_fourier_closure_eq_top]
    trivial
  let η := ε / (4 * (‖F‖ + 1))
  have hη : 0 < η := by dsimp [η]; positivity
  obtain ⟨p, hp, hclose⟩ := Metric.mem_closure_iff.mp hdense η hη
  have hpbound : ∀ t, |(p t).re - h t| ≤ η := by
    intro t
    calc
      _ = |(hc t - p t).re| := by simp only [hc, Complex.sub_re];
                                               exact abs_sub_comm _ _
      _ ≤ ‖hc t - p t‖ := Complex.abs_re_le_norm _
      _ ≤ ‖hc - p‖ := (hc - p).norm_coe_le_norm t
      _ ≤ η := by simpa only [dist_eq_norm] using hclose.le
  have hdiff : ‖(∫ t, (p t).re • F t ∂μ) - ∫ t, h t • F t ∂μ‖ ≤ η * ‖F‖ := by
    have hi₁ : Integrable (fun t ↦ (p t).re • F t) μ :=
      hint ⟨_, (Complex.continuous_re.comp p.continuous).smul F.continuous⟩
    have hi₂ : Integrable (fun t ↦ h t • F t) μ :=
      hint ⟨_, h.continuous.smul F.continuous⟩
    rw [← integral_sub hi₁ hi₂]
    have hb : ∀ t, ‖(p t).re • F t - h t • F t‖ ≤ η * ‖F‖ := by
      intro t
      rw [← sub_smul, norm_smul, Real.norm_eq_abs]
      exact mul_le_mul (hpbound t) (F.norm_coe_le_norm t) (norm_nonneg _) hη.le
    simpa [μ, measureReal_def] using
      norm_integral_le_of_norm_le_const (μ := μ) (Filter.Eventually.of_forall hb)
  have hηbound : η * ‖F‖ ≤ ε / 4 := by
    have heq : η * (‖F‖ + 1) = ε / 4 := by
      dsimp [η]
      field_simp
    nlinarith [norm_nonneg F]
  refine ⟨p, hp, ?_⟩
  calc
    _ ≤ ‖(∫ t, (p t).re • F t ∂μ) - ∫ t, h t • F t ∂μ‖ +
        ‖(∫ t, h t • F t ∂μ) - F 0‖ := norm_sub_le_norm_sub_add_norm_sub _ _ _
    _ ≤ ε / 4 + ε / 4 := add_le_add (hdiff.trans hηbound) havg
    _ < ε := by linarith

#print axioms planar_fourier_kernel_approximation

end GlobalEmbedding.Paper
