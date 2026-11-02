import GlobalEmbedding.Offline.BufferedModelCoordinates
import GlobalEmbedding.Offline.PaperShiftedSmoothing

/-!
# Buffered smoothing estimates in the original source model

Source: `main.tex` 700–720 and the original Euclidean atlas coordinate ABI.
The convolution, buffer balls, transitions, and global map all remain on the
original model E. Component norms use the actual fixed linear-equivalence
coordinates, with both operator-norm factors explicitly proved and retained.
The source evaluation domains are genuine fixed sampling buffers, and output
evaluation domains are the original inner charts. No atlas is reconstructed.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d q : ℕ} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The original atlas Cj maximum of the SAME global error follows from actual
local error jets, including every cutoff/transition term and support multiplicity. -/
theorem paperAtlasCj_model_buffered_error_le_of_local (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (j : ℕ) (R : ℝ) (hR : 0 ≤ R)
    (hlocal : ∀ i k, k ≤ j → ∀ y ∈ bufferedInnerCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedLocalError A mu K ell u i) y‖ ≤ R) :
    let e := bufferedModelCoordinates A c (bufferedSmoothing A mu K ell chi u - u)
    let O := bufferedModelTargets A c
    paperAtlasCj j e O (bufferedModelInner A c) ≠ ⊤ ∧
      (paperAtlasCj j e O (bufferedModelInner A c)).toReal ≤
        modelBufferedTransferConstant c B T D j * R := by
  dsimp only
  let enative := bufferedNativeCoordinates A (bufferedSmoothing A mu K ell chi u - u)
  let Onative := fun i => (A.chart i).target
  have he : ∀ i, ContDiffOn ℝ ∞ (enative i) (Onative i) :=
    bufferedNativeCoordinates_contDiffOn A hA
      ((bufferedSmoothing_contMDiff A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport hu).sub hu)
  have hbound : ∀ p, ∀ k ≤ j, ∀ y ∈ bufferedInnerCoordinates A p,
      ‖iteratedFDeriv ℝ k (enative p) y‖ ≤ bufferedTransferConstant B T D j * R := by
    intro p k hk y hy
    exact bufferedSmoothing_chart_jet_le A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport
      hpartition hu B T hB hT D p hy.1 (hD _) j k hk R hR
      (fun i hi a => hweight p i a y hy hi)
      (fun i hi a ha => htransition p i a ha y hy hi)
      (fun i hi a ha => hlocal i a ha _ (bufferedInnerCoordinates_mem A i (hchiSupport i hi)))
  have hQR := mul_nonneg (bufferedTransferConstant_nonneg hB hT D j) hR
  have hle := paperAtlasCj_model_le_of_native_bound c j enative Onative (bufferedInnerCoordinates A)
    (fun i => (A.chart i).open_target) (fun _ _ hy => hy.1) he _ hQR hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal (mul_nonneg (linearModelFactor_nonneg _ _) hQR)] at hr
  simpa only [enative, Onative, bufferedModelCoordinates, bufferedModelTargets,
    bufferedModelInner, modelBufferedTransferConstant, mul_assoc] using hr

/-- Low-order original C^(j+base) tail for the ACTUAL global map.
The r-moment kernel uses only original source C^(r+base) on the genuine fixed
sampling buffers. No error bound or local desired tail is assumed. -/
theorem paperAtlasCj_model_buffered_error_low (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {kappa : E → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base r j : ℕ) (hjr : j ≤ r)
    {rho ell : ℝ} (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hfinite : paperAtlasCj (r + base) (bufferedModelCoordinates A c u)
      (bufferedModelTargets A c) (bufferedModelSampling A c) ≠ ⊤) :
    let K := finiteMomentKernel r kappa
    let e := bufferedModelCoordinates A c (bufferedSmoothing A mu K ell chi u - u)
    let O := bufferedModelTargets A c
    paperAtlasCj (j + base) e O (bufferedModelInner A c) ≠ ⊤ ∧
      (paperAtlasCj (j + base) e O (bufferedModelInner A c)).toReal ≤
        (modelBufferedTransferConstant c B T D (j + base) * kernelTailConstant mu K r *
          nativeCoordinateFactor c (r + base)) * ell ^ (r - j) *
            (paperAtlasCj (r + base) (bufferedModelCoordinates A c u) O (bufferedModelSampling A c)).toReal := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let O := bufferedModelTargets A c
  let I := (paperAtlasCj (r + base) (bufferedModelCoordinates A c u) O (bufferedModelSampling A c)).toReal
  let P := nativeCoordinateFactor c (r + base) * I
  let R := kernelTailConstant mu K r * P * ell ^ (r - j)
  have hP : 0 ≤ P := mul_nonneg (nativeCoordinateFactor_nonneg c _) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelTailConstant_nonneg mu K r) hP) (pow_nonneg hell _)
  have hsource : ∀ i k, k ≤ r + base → ∀ y ∈ bufferedSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedCoordinateExtension A u i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_bufferedCoordinateExtension A u i k (bufferedSampling_subset_target A i hy)]
    exact paperAtlasCj_model_native_jet_le c (r + base) (bufferedNativeCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (bufferedSampling_subset_target A)
      (bufferedNativeCoordinates_contDiffOn A hA hu) hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j + base → ∀ y ∈ bufferedInnerCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedLocalError A mu K ell u i) y‖ ≤ R := by
    intro i k hk y hy
    exact signedSmoothing_low_shifted_derivative_error_le mu hsmooth hcompact hmass base r j hjr
      (bufferedInnerCoordinates_open A i) (bufferedSamplingCoordinates_open A i)
      (bufferedInner_subset_sampling A i)
      ((bufferedCoordinateExtension_contDiffOn A hA hu i).mono (bufferedSampling_subset_target A i)) hell
      (fun z hz w hw s hs => buffered_kernel_segment_mem_sampling A i hsupp hrho hell hell1 hz hw hs)
      P hP (hsource i) hk hy
  have h := paperAtlasCj_model_buffered_error_le_of_local A c hA mu (finiteMomentKernel_contDiff hsmooth r)
    (finiteMomentKernel_hasCompactSupport hcompact r) hsupp hrho hell hell1 chi hchi hchiSupport
    hpartition hu B T hB hT D hD hweight htransition (j + base) R hR hlocal
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp [R, P, I]
  ring

/-- The same-order signed-L1 estimate in the original Cj norm after ALL actual
global cutoff/transition terms. It controls high weighted orders and proves
genuine output finiteness even when the source chart domains are unbounded. -/
theorem paperAtlasCj_model_buffered_error_high (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (j : ℕ) (hfinite : paperAtlasCj j (bufferedModelCoordinates A c u)
      (bufferedModelTargets A c) (bufferedModelSampling A c) ≠ ⊤) :
    let e := bufferedModelCoordinates A c (bufferedSmoothing A mu K ell chi u - u)
    let O := bufferedModelTargets A c
    paperAtlasCj j e O (bufferedModelInner A c) ≠ ⊤ ∧
      (paperAtlasCj j e O (bufferedModelInner A c)).toReal ≤
        (modelBufferedTransferConstant c B T D j * (1 + ∫ y, |K y| ∂mu) * nativeCoordinateFactor c j) *
          (paperAtlasCj j (bufferedModelCoordinates A c u) O (bufferedModelSampling A c)).toReal := by
  dsimp only
  let O := bufferedModelTargets A c
  let I := (paperAtlasCj j (bufferedModelCoordinates A c u) O (bufferedModelSampling A c)).toReal
  let P := nativeCoordinateFactor c j * I
  let R := (1 + ∫ y, |K y| ∂mu) * P
  have hP : 0 ≤ P := mul_nonneg (nativeCoordinateFactor_nonneg c _) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg
    (add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))) hP
  have hsource : ∀ i k, k ≤ j → ∀ y ∈ bufferedSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedCoordinateExtension A u i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_bufferedCoordinateExtension A u i k (bufferedSampling_subset_target A i hy)]
    exact paperAtlasCj_model_native_jet_le c j (bufferedNativeCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (bufferedSampling_subset_target A)
      (bufferedNativeCoordinates_contDiffOn A hA hu) hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j → ∀ y ∈ bufferedInnerCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedLocalError A mu K ell u i) y‖ ≤ R := by
    intro i k hk y hy
    apply signedSmoothing_derivative_error_le_L1 mu hK hcompact (bufferedInnerCoordinates_open A i)
      (bufferedSamplingCoordinates_open A i) (bufferedInner_subset_sampling A i)
      ((bufferedCoordinateExtension_contDiffOn A hA hu i).mono (bufferedSampling_subset_target A i)) ell
      (fun z hz w hw => ?_) k hy P (hsource i k hk)
    simpa only [one_smul] using buffered_kernel_segment_mem_sampling A i hsupp hrho hell hell1 hz hw
      (s := 1) (by simp)
  have h := paperAtlasCj_model_buffered_error_le_of_local A c hA mu hK hcompact hsupp hrho hell hell1 chi hchi
    hchiSupport hpartition hu B T hB hT D hD hweight htransition j R hR hlocal
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp [R, P, I]
  ring

end

end GlobalEmbedding.Offline
