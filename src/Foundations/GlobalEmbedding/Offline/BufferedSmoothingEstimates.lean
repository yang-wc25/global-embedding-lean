import GlobalEmbedding.Offline.BufferedSmoothingJets
import GlobalEmbedding.Offline.BufferedSamplingDomains
import GlobalEmbedding.Offline.PaperShiftedSmoothing

/-!
# The same global smoothing error in the original cumulative coordinate norms

Source: `main.tex` 700–720 and `repair-buffered-smoothing-localization`.
Both norm families are actual pullbacks of ONE manifold map through the
original atlas. Input norms differentiate on the original chart targets and
evaluate on their fixed genuine sampling buffers. Output norms differentiate
on those same targets and evaluate on the original inner coordinates.

All cutoff/transition derivatives and overlap multiplicity are genuine
uniform-data provider inputs. Local errors are subsequently derived from
source norms and the fixed signed kernel. Output finiteness is proved before
real projection. No chart-count factor or independent gluing premise occurs.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

variable {d q : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℝ) M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

/-- The original chart representatives of one actual manifold map. -/
def bufferedAtlasCoordinates (A : BufferedAtlas M (Fin d → ℝ)) (u : M → Fin q → ℝ) :=
  fun i : Fin A.count => u ∘ (A.chart i).symm

/-- Genuine source smoothness gives smoothness of its actual chart representatives. -/
theorem bufferedAtlasCoordinates_contDiffOn (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) {u : M → Fin q → ℝ}
    (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ u) (i : Fin A.count) :
    ContDiffOn ℝ ∞ (bufferedAtlasCoordinates A u i) (A.chart i).target :=
  (hu.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA.chart_mem i))).contDiffOn

/-- The original atlas Cj maximum of the SAME global error follows from actual
local error jets, including every cutoff/transition term and support multiplicity. -/
theorem paperAtlasCj_buffered_error_le_of_local (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure (Fin d → ℝ)) [mu.IsAddHaarMeasure]
    {K : (Fin d → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ u)
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
    let e := bufferedAtlasCoordinates A (bufferedSmoothing A mu K ell chi u - u)
    let O := fun i => (A.chart i).target
    paperAtlasCj j e O (bufferedInnerCoordinates A) ≠ ⊤ ∧
      (paperAtlasCj j e O (bufferedInnerCoordinates A)).toReal ≤
        bufferedTransferConstant B T D j * R := by
  dsimp only
  let e := bufferedAtlasCoordinates A (bufferedSmoothing A mu K ell chi u - u)
  let O := fun i => (A.chart i).target
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i) :=
    bufferedAtlasCoordinates_contDiffOn A hA
      ((bufferedSmoothing_contMDiff A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport hu).sub hu)
  have hbound : ∀ p, ∀ k ≤ j, ∀ y ∈ bufferedInnerCoordinates A p,
      ‖iteratedFDeriv ℝ k (e p) y‖ ≤ bufferedTransferConstant B T D j * R := by
    intro p k hk y hy
    exact bufferedSmoothing_chart_jet_le A hA mu hK hcompact hsupp hrho hell hell1 chi hchi hchiSupport
      hpartition hu B T hB hT D p hy.1 (hD _) j k hk R hR
      (fun i hi a => hweight p i a y hy hi)
      (fun i hi a ha => htransition p i a ha y hy hi)
      (fun i hi a ha => hlocal i a ha _ (bufferedInnerCoordinates_mem A i (hchiSupport i hi)))
  have hle := paperAtlasCj_le_of_jet_bound j e O (bufferedInnerCoordinates A)
    (fun i => (A.chart i).open_target) (fun _ _ hy => hy.1) he _ hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rwa [ENNReal.toReal_ofReal (mul_nonneg (bufferedTransferConstant_nonneg hB hT D j) hR)] at hr

/-- Low-order original C^(j+base) tail for the ACTUAL global map.
The r-moment kernel uses only original source C^(r+base) on the genuine fixed
sampling buffers. No error bound or local desired tail is assumed. -/
theorem paperAtlasCj_buffered_error_low (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure (Fin d → ℝ)) [mu.IsAddHaarMeasure]
    {kappa : (Fin d → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base r j : ℕ) (hjr : j ≤ r)
    {rho ell : ℝ} (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hfinite : paperAtlasCj (r + base) (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤) :
    let K := finiteMomentKernel r kappa
    let e := bufferedAtlasCoordinates A (bufferedSmoothing A mu K ell chi u - u)
    let O := fun i => (A.chart i).target
    paperAtlasCj (j + base) e O (bufferedInnerCoordinates A) ≠ ⊤ ∧
      (paperAtlasCj (j + base) e O (bufferedInnerCoordinates A)).toReal ≤
        (bufferedTransferConstant B T D (j + base) * kernelTailConstant mu K r *
          coordinateDimensionFactor d (r + base)) * ell ^ (r - j) *
            (paperAtlasCj (r + base) (bufferedAtlasCoordinates A u) O (bufferedSamplingCoordinates A)).toReal := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let O := fun i => (A.chart i).target
  let I := (paperAtlasCj (r + base) (bufferedAtlasCoordinates A u) O (bufferedSamplingCoordinates A)).toReal
  let P := coordinateDimensionFactor d (r + base) * I
  let R := kernelTailConstant mu K r * P * ell ^ (r - j)
  have hP : 0 ≤ P := mul_nonneg (coordinateDimensionFactor_nonneg d _) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelTailConstant_nonneg mu K r) hP) (pow_nonneg hell _)
  have hsource : ∀ i k, k ≤ r + base → ∀ y ∈ bufferedSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedCoordinateExtension A u i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_bufferedCoordinateExtension A u i k (bufferedSampling_subset_target A i hy)]
    exact paperAtlasCj_jet_le (r + base) (bufferedAtlasCoordinates A u) O (bufferedSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (bufferedSampling_subset_target A)
      (bufferedAtlasCoordinates_contDiffOn A hA hu) hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j + base → ∀ y ∈ bufferedInnerCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedLocalError A mu K ell u i) y‖ ≤ R := by
    intro i k hk y hy
    exact signedSmoothing_low_shifted_derivative_error_le mu hsmooth hcompact hmass base r j hjr
      (bufferedInnerCoordinates_open A i) (bufferedSamplingCoordinates_open A i)
      (bufferedInner_subset_sampling A i)
      ((bufferedCoordinateExtension_contDiffOn A hA hu i).mono (bufferedSampling_subset_target A i)) hell
      (fun z hz w hw s hs => buffered_kernel_segment_mem_sampling A i hsupp hrho hell hell1 hz hw hs)
      P hP (hsource i) hk hy
  have h := paperAtlasCj_buffered_error_le_of_local A hA mu (finiteMomentKernel_contDiff hsmooth r)
    (finiteMomentKernel_hasCompactSupport hcompact r) hsupp hrho hell hell1 chi hchi hchiSupport
    hpartition hu B T hB hT D hD hweight htransition (j + base) R hR hlocal
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp [R, P, I]
  ring

/-- The same-order signed-L1 estimate in the original Cj norm after ALL actual
global cutoff/transition terms. It controls high weighted orders and proves
genuine output finiteness even when the source chart domains are unbounded. -/
theorem paperAtlasCj_buffered_error_high (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure (Fin d → ℝ)) [mu.IsAddHaarMeasure]
    {K : (Fin d → ℝ) → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (j : ℕ) (hfinite : paperAtlasCj j (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤) :
    let e := bufferedAtlasCoordinates A (bufferedSmoothing A mu K ell chi u - u)
    let O := fun i => (A.chart i).target
    paperAtlasCj j e O (bufferedInnerCoordinates A) ≠ ⊤ ∧
      (paperAtlasCj j e O (bufferedInnerCoordinates A)).toReal ≤
        (bufferedTransferConstant B T D j * (1 + ∫ y, |K y| ∂mu) * coordinateDimensionFactor d j) *
          (paperAtlasCj j (bufferedAtlasCoordinates A u) O (bufferedSamplingCoordinates A)).toReal := by
  dsimp only
  let O := fun i => (A.chart i).target
  let I := (paperAtlasCj j (bufferedAtlasCoordinates A u) O (bufferedSamplingCoordinates A)).toReal
  let P := coordinateDimensionFactor d j * I
  let R := (1 + ∫ y, |K y| ∂mu) * P
  have hP : 0 ≤ P := mul_nonneg (coordinateDimensionFactor_nonneg d _) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg
    (add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))) hP
  have hsource : ∀ i k, k ≤ j → ∀ y ∈ bufferedSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedCoordinateExtension A u i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_bufferedCoordinateExtension A u i k (bufferedSampling_subset_target A i hy)]
    exact paperAtlasCj_jet_le j (bufferedAtlasCoordinates A u) O (bufferedSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (bufferedSampling_subset_target A)
      (bufferedAtlasCoordinates_contDiffOn A hA hu) hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j → ∀ y ∈ bufferedInnerCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedLocalError A mu K ell u i) y‖ ≤ R := by
    intro i k hk y hy
    apply signedSmoothing_derivative_error_le_L1 mu hK hcompact (bufferedInnerCoordinates_open A i)
      (bufferedSamplingCoordinates_open A i) (bufferedInner_subset_sampling A i)
      ((bufferedCoordinateExtension_contDiffOn A hA hu i).mono (bufferedSampling_subset_target A i)) ell
      (fun z hz w hw => ?_) k hy P (hsource i k hk)
    simpa only [one_smul] using buffered_kernel_segment_mem_sampling A i hsupp hrho hell hell1 hz hw
      (s := 1) (by simp)
  have h := paperAtlasCj_buffered_error_le_of_local A hA mu hK hcompact hsupp hrho hell hell1 chi hchi
    hchiSupport hpartition hu B T hB hT D hD hweight htransition j R hR hlocal
  refine ⟨h.1, h.2.trans_eq ?_⟩
  dsimp [R, P, I]
  ring

end

end GlobalEmbedding.Offline
