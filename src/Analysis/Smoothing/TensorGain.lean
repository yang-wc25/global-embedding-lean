import Smoothing.TensorGainJets
import Smoothing.TensorModelCoordinates
import GlobalEmbedding.Offline.LocalKernelGain

/-!
# Actual global derivative gain from the true low-order source norm

Source: `main.tex` 700–720, gain from the genuine C0 actual tensor input.
The same global tensor smoother is localized using its actual cutoff and chart
transition derivatives. Local gain uses a bounded indicator only to prove
local integrability; neighborhood equality returns every derivative to the
original operator. The final norm is the frozen original cumulative chart
maximum, on actual component coordinates of the original source model.
No compact support or global integrability of the original source is assumed.
-/

open Module MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d n : ℕ} {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual global cumulative C^(j+base) bound costs only ell^-j times
the true original C^base source bound. The source norm is evaluated on fixed
sampling buffers; the output norm is on original inner domains. Every native
cutoff/transition term and the actual support multiplicity is included. -/
theorem paperAtlasCj_model_tensor_smoothing_gain (A : BufferedAtlas M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho) (hrho : rho ≤ A.buffer)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (b : Fin A.count → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ p i a r, ContDiffOn ℝ ∞ (tensorFrameTransition A b p i a r)
      (bufferedChartOverlap A p i))
    (B T J : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hframeBound : ∀ p i a r k, ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (tensorFrameTransition A b p i a r) y‖ ≤ J k)
    (base j : ℕ) (hfinite : paperAtlasCj base (bufferedTensorModelCoordinates A c b H)
      (bufferedModelTargets A c) (bufferedModelSampling A c) ≠ ⊤) :
    let f := modelCoordinateFamily c (bufferedTensorSmoothingCoordinates A mu K ell chi b H)
    let O := bufferedModelTargets A c
    paperAtlasCj (j + base) f O (bufferedModelInner A c) ≠ ⊤ ∧
      (paperAtlasCj (j + base) f O (bufferedModelInner A c)).toReal ≤
        (modelTensorTransferConstant n c B T J D (j + base) * kernelGainConstant mu K j *
          nativeCoordinateFactor c base) * (ell⁻¹)^j *
          (paperAtlasCj base (bufferedTensorModelCoordinates A c b H) O (bufferedModelSampling A c)).toReal := by
  dsimp only
  let I := (paperAtlasCj base (bufferedTensorModelCoordinates A c b H)
    (bufferedModelTargets A c) (bufferedModelSampling A c)).toReal
  let P := nativeCoordinateFactor c base * I
  let R := kernelGainConstant mu K j * P * (ell⁻¹)^j
  have hP : 0 ≤ P := mul_nonneg (nativeCoordinateFactor_nonneg c base) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelGainConstant_nonneg mu K j) hP)
    (pow_nonneg (inv_nonneg.mpr hell.le) _)
  have hsource : ∀ i k, k ≤ base → ∀ y ∈ bufferedSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedCoordinateExtension A (tensorCoefficientField A b H i) i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_bufferedCoordinateExtension A (tensorCoefficientField A b H i) i k (bufferedSampling_subset_target A i hy)]
    exact paperAtlasCj_model_native_jet_le c base (bufferedTensorNativeCoordinates A b H)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (bufferedSampling_subset_target A)
      hH hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j + base → ∀ y ∈ bufferedInnerCoordinates A i,
      ‖iteratedFDeriv ℝ k (bufferedLocalSmoothing A mu K ell (tensorCoefficientField A b H i) i) y‖ ≤ R := by
    intro i k hk y hy
    apply signedSmoothing_local_cumulative_gain mu hK hcompact
      (bufferedInnerCoordinates_open A i) (bufferedSamplingCoordinates_open A i)
      ((tensorCoordinateExtension_contDiffOn A b H i (hH i)).mono (bufferedSampling_subset_target A i))
      hell hell1 _ base j P hP (hsource i) hk hy
    intro z hz w hw
    simpa only [one_smul] using buffered_kernel_segment_mem_sampling A i hsupp hrho hell.le hell1 hz hw
      (s := 1) (by simp)
  let f := bufferedTensorSmoothingCoordinates A mu K ell chi b H
  let O := fun i => (A.chart i).target
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    bufferedTensorSmoothingCoordinates_contDiffOn A hA mu hK hcompact hsupp hrho hell.le hell1
      chi hchi hchiSupport b H hH hframe
  have hbound : ∀ p, ∀ k ≤ j + base, ∀ y ∈ bufferedInnerCoordinates A p,
      ‖iteratedFDeriv ℝ k (f p) y‖ ≤ tensorTransferConstant n B T J D (j + base) * R := by
    intro p k hk y hy
    exact bufferedTensorSmoothingCoordinates_jet_le A hA mu hK hcompact hsupp hrho hell.le hell1 chi hchi hchiSupport
      b H hH hframe B T J hB hT hJ D p hy.1 (hD _) (j + base) k hk R hR
      (fun i hi a => hweight p i a y hy hi)
      (fun i hi a ha => htransition p i a ha y hy hi)
      (fun i hi a r k => hframeBound p i a r k y hy hi)
      (fun i hi a ha => hlocal i a ha _ (bufferedInnerCoordinates_mem A i (hchiSupport i hi)))
  have hQR := mul_nonneg (tensorTransferConstant_nonneg n hB hT hJ D (j + base)) hR
  have hle := paperAtlasCj_model_le_of_native_bound c (j + base) f O (bufferedInnerCoordinates A)
    (fun i => (A.chart i).open_target) (fun _ _ hy => hy.1) hf _ hQR hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal (mul_nonneg (linearModelFactor_nonneg _ _) hQR)] at hr
  change (paperAtlasCj (j + base) (modelCoordinateFamily c (bufferedTensorSmoothingCoordinates A mu K ell chi b H))
      (bufferedModelTargets A c) (bufferedModelInner A c)).toReal ≤ _ at hr
  apply hr.trans_eq
  unfold modelTensorTransferConstant
  dsimp only [R, P, I]
  ring

end

end GlobalEmbedding.Offline
