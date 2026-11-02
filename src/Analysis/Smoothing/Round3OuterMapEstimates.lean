import Smoothing.Round3OuterDomains
import Smoothing.ParameterLocalMapEstimates
import Smoothing.ParameterLocalMapJets
import Smoothing.TensorLocalModelDomains
import GlobalEmbedding.Offline.PaperShiftedSmoothing

/-! Same actual smoother with receiving estimates on full chart targets.
Only active convolution centers require the original buffered inner charts.
The original constants, sampling buffers and native two-frame tensor formula
are unchanged. The old receiving-inner restriction is removed. -/

open GlobalEmbedding.Offline MeasureTheory GlobalEmbedding.Paper Function Set Filter Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Continuation

noncomputable section

variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d q : ℕ} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original atlas Cj maximum of the SAME global error follows from actual
local error jets, including every cutoff/transition term and support multiplicity. -/
theorem round3Outer_paperAtlasCj_model_parameterLocalMap_error_le_of_local (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (U : Set M) (hU : IsOpen U) (hpartition : ∀ x ∈ U, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ (A.chart p).target, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (j : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hlocal : ∀ i k, k ≤ j → ∀ y ∈ tensorLocalInner A i,
      ‖iteratedFDeriv ℝ k (parameterLocalMapError A mu K ell u i) y‖ ≤ R) :
    let e := parameterLocalMapModelCoordinates A c (parameterLocalMapSmoothing A mu K ell chi u - u)
    let O := tensorLocalModelTargets A c
    paperAtlasCj j e O (round3OuterModelEvaluation A c U) ≠ ⊤ ∧
      (paperAtlasCj j e O (round3OuterModelEvaluation A c U)).toReal ≤
        modelBufferedTransferConstant c B T D j * R := by
  dsimp only
  let enative := parameterLocalMapNativeCoordinates A (parameterLocalMapSmoothing A mu K ell chi u - u)
  let Onative := fun i => (A.chart i).target
  have hs := parameterLocalMapSmoothing_contMDiff A hA mu hK hcompact hsupp hrho hell hell1
    chi hchi hchiSupport u hu
  have he : ∀ i, ContDiffOn ℝ ∞ (enative i) (Onative i) := by
    intro i
    exact (hs.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA i))).contDiffOn.sub (hu i)
  have hbound : ∀ p, ∀ k ≤ j, ∀ y ∈ round3OuterEvaluation A U p,
      ‖iteratedFDeriv ℝ k (enative p) y‖ ≤ bufferedTransferConstant B T D j * R := by
    intro p k hk y hy
    have hpart : ∀ᶠ z in 𝓝 y, ∑ i, chi i ((A.chart p).symm z)^2 = 1 := by
      filter_upwards [((A.chart p).symm.continuousAt hy.1).preimage_mem_nhds (hU.mem_nhds hy.2)] with z hz
      exact hpartition _ hz
    exact parameterLocalMapSmoothing_chart_jet_le A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport
      hu B T hB hT D p hy.1 hpart (hD _) j k hk R hR
      (fun i hi a => hweight p i a y hy.1 hi)
      (fun i hi a ha => htransition p i a ha y hy.1 hi)
      (fun i hi a ha => hlocal i a ha _ (tensorLocalInner_mem A i (hchiSupport i hi)))
  have hQR := mul_nonneg (bufferedTransferConstant_nonneg hB hT D j) hR
  have hle := paperAtlasCj_model_le_of_native_bound c j enative Onative (round3OuterEvaluation A U)
    (fun i => (A.chart i).open_target) (fun _ _ hy => hy.1) he _ hQR hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal (mul_nonneg (linearModelFactor_nonneg _ _) hQR)] at hr
  simpa only [enative, Onative, parameterLocalMapModelCoordinates, tensorLocalModelTargets,
    round3OuterModelEvaluation, modelBufferedTransferConstant, mul_assoc] using hr

/-- Low-order original C^(j+base) tail for the ACTUAL global map.
The r-moment kernel uses only original source C^(r+base) on the genuine fixed
sampling buffers. No error bound or local desired tail is assumed. -/
theorem round3Outer_paperAtlasCj_model_parameterLocalMap_error_low (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {kappa : E → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base r j : ℕ) (hjr : j ≤ r)
    {rho ell : ℝ} (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (U : Set M) (hU : IsOpen U) (hpartition : ∀ x ∈ U, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ (A.chart p).target, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hfinite : paperAtlasCj (r + base) (parameterLocalMapModelCoordinates A c u)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤) :
    let K := finiteMomentKernel r kappa
    let e := parameterLocalMapModelCoordinates A c (parameterLocalMapSmoothing A mu K ell chi u - u)
    let O := tensorLocalModelTargets A c
    paperAtlasCj (j + base) e O (round3OuterModelEvaluation A c U) ≠ ⊤ ∧
      (paperAtlasCj (j + base) e O (round3OuterModelEvaluation A c U)).toReal ≤
        (modelBufferedTransferConstant c B T D (j + base) * kernelTailConstant mu K r *
          nativeCoordinateFactor c (r + base)) * ell ^ (r - j) *
            (paperAtlasCj (r + base) (parameterLocalMapModelCoordinates A c u) O (tensorLocalModelSampling A c)).toReal := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let O := tensorLocalModelTargets A c
  let I := (paperAtlasCj (r + base) (parameterLocalMapModelCoordinates A c u) O (tensorLocalModelSampling A c)).toReal
  let P := nativeCoordinateFactor c (r + base) * I
  let R := kernelTailConstant mu K r * P * ell ^ (r - j)
  have hP : 0 ≤ P := mul_nonneg (nativeCoordinateFactor_nonneg c _) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelTailConstant_nonneg mu K r) hP) (pow_nonneg hell _)
  have hsource : ∀ i k, k ≤ r + base → ∀ y ∈ tensorLocalSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (tensorLocalCoordinateExtension A u i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_tensorLocalCoordinateExtension A u i k (tensorLocalSampling_subset_target A i hy)]
    exact paperAtlasCj_model_native_jet_le c (r + base) (parameterLocalMapNativeCoordinates A u)
      (fun i => (A.chart i).target) (tensorLocalSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (tensorLocalSampling_subset_target A)
      hu hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j + base → ∀ y ∈ tensorLocalInner A i,
      ‖iteratedFDeriv ℝ k (parameterLocalMapError A mu K ell u i) y‖ ≤ R := by
    intro i k hk y hy
    exact signedSmoothing_low_shifted_derivative_error_le mu hsmooth hcompact hmass base r j hjr
      (tensorLocalInner_open A i) (tensorLocalSamplingCoordinates_open A i)
      (tensorLocalInner_subset_sampling A i)
      ((tensorLocalCoordinateExtension_contDiffOn A u i (hu i)).mono (tensorLocalSampling_subset_target A i)) hell
      (fun z hz w hw s hs => tensorLocal_kernel_segment_mem_sampling A i hsupp hrho hell hell1 hz hw hs)
      P hP (hsource i) hk hy
  have h := round3Outer_paperAtlasCj_model_parameterLocalMap_error_le_of_local A c hA mu (finiteMomentKernel_contDiff hsmooth r)
    (finiteMomentKernel_hasCompactSupport hcompact r) hsupp hrho hell hell1 chi hchi hchiSupport
    U hU hpartition hu B T hB hT D hD hweight htransition (j + base) R hR hlocal
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp [R, P, I]
  ring

/-- The same-order signed-L1 estimate in the original Cj norm after ALL actual
global cutoff/transition terms. It controls high weighted orders and proves
genuine output finiteness even when the source chart domains are unbounded. -/
theorem round3Outer_paperAtlasCj_model_parameterLocalMap_error_high (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (U : Set M) (hU : IsOpen U) (hpartition : ∀ x ∈ U, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ (A.chart p).target, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (j : ℕ) (hfinite : paperAtlasCj j (parameterLocalMapModelCoordinates A c u)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤) :
    let e := parameterLocalMapModelCoordinates A c (parameterLocalMapSmoothing A mu K ell chi u - u)
    let O := tensorLocalModelTargets A c
    paperAtlasCj j e O (round3OuterModelEvaluation A c U) ≠ ⊤ ∧
      (paperAtlasCj j e O (round3OuterModelEvaluation A c U)).toReal ≤
        (modelBufferedTransferConstant c B T D j * (1 + ∫ y, |K y| ∂mu) * nativeCoordinateFactor c j) *
          (paperAtlasCj j (parameterLocalMapModelCoordinates A c u) O (tensorLocalModelSampling A c)).toReal := by
  dsimp only
  let O := tensorLocalModelTargets A c
  let I := (paperAtlasCj j (parameterLocalMapModelCoordinates A c u) O (tensorLocalModelSampling A c)).toReal
  let P := nativeCoordinateFactor c j * I
  let R := (1 + ∫ y, |K y| ∂mu) * P
  have hP : 0 ≤ P := mul_nonneg (nativeCoordinateFactor_nonneg c _) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg
    (add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))) hP
  have hsource : ∀ i k, k ≤ j → ∀ y ∈ tensorLocalSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (tensorLocalCoordinateExtension A u i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_tensorLocalCoordinateExtension A u i k (tensorLocalSampling_subset_target A i hy)]
    exact paperAtlasCj_model_native_jet_le c j (parameterLocalMapNativeCoordinates A u)
      (fun i => (A.chart i).target) (tensorLocalSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (tensorLocalSampling_subset_target A)
      hu hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j → ∀ y ∈ tensorLocalInner A i,
      ‖iteratedFDeriv ℝ k (parameterLocalMapError A mu K ell u i) y‖ ≤ R := by
    intro i k hk y hy
    apply signedSmoothing_derivative_error_le_L1 mu hK hcompact (tensorLocalInner_open A i)
      (tensorLocalSamplingCoordinates_open A i) (tensorLocalInner_subset_sampling A i)
      ((tensorLocalCoordinateExtension_contDiffOn A u i (hu i)).mono (tensorLocalSampling_subset_target A i)) ell
      (fun z hz w hw => ?_) k hy P (hsource i k hk)
    simpa only [one_smul] using tensorLocal_kernel_segment_mem_sampling A i hsupp hrho hell hell1 hz hw
      (s := 1) (by simp)
  have h := round3Outer_paperAtlasCj_model_parameterLocalMap_error_le_of_local A c hA mu hK hcompact hsupp hrho hell hell1 chi hchi
    hchiSupport U hU hpartition hu B T hB hT D hD hweight htransition j R hR hlocal
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp [R, P, I]
  ring

#print axioms round3Outer_paperAtlasCj_model_parameterLocalMap_error_low
#print axioms round3Outer_paperAtlasCj_model_parameterLocalMap_error_high
end

end GlobalEmbedding.Continuation
