import Smoothing.Round3OuterDomains
import Smoothing.TensorLocalGain
import Smoothing.TensorLocalGainJets
import Smoothing.TensorLocalModelDomains
import GlobalEmbedding.Offline.LocalKernelGain

/-! Same actual smoother with receiving estimates on full chart targets.
Only active convolution centers require the original buffered inner charts.
The original constants, sampling buffers and native two-frame tensor formula
are unchanged. The old receiving-inner restriction is removed. -/

open Module MeasureTheory GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d n : ℕ} {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual global cumulative C^(j+base) bound costs only ell^-j times
the true original C^base source bound. The source norm is evaluated on fixed
sampling buffers; the output norm is on full receiving chart targets. Every native
cutoff/transition term and the actual support multiplicity is included. -/
theorem round3Outer_paperAtlasCj_model_local_tensor_smoothing_gain (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho) (hrho : rho ≤ A.buffer)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorLocalCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ p i a r, ContDiffOn ℝ ∞ (tensorLocalFrameTransition A b p i a r)
      (tensorLocalChartOverlap A p i))
    (B T J : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hframeBound : ∀ p i a r k, ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (tensorLocalFrameTransition A b p i a r) y‖ ≤ J k)
    (base j : ℕ) (hfinite : paperAtlasCj base (tensorLocalModelCoordinates A c b H)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤) :
    let f := modelCoordinateFamily c (tensorLocalSmoothingCoordinates A mu K ell chi b H)
    let O := tensorLocalModelTargets A c
    paperAtlasCj (j + base) f O (tensorLocalModelTargets A c) ≠ ⊤ ∧
      (paperAtlasCj (j + base) f O (tensorLocalModelTargets A c)).toReal ≤
        (modelTensorTransferConstant n c B T J D (j + base) * kernelGainConstant mu K j *
          nativeCoordinateFactor c base) * (ell⁻¹)^j *
          (paperAtlasCj base (tensorLocalModelCoordinates A c b H) O (tensorLocalModelSampling A c)).toReal := by
  dsimp only
  let I := (paperAtlasCj base (tensorLocalModelCoordinates A c b H)
    (tensorLocalModelTargets A c) (tensorLocalModelSampling A c)).toReal
  let P := nativeCoordinateFactor c base * I
  let R := kernelGainConstant mu K j * P * (ell⁻¹)^j
  have hP : 0 ≤ P := mul_nonneg (nativeCoordinateFactor_nonneg c base) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelGainConstant_nonneg mu K j) hP)
    (pow_nonneg (inv_nonneg.mpr hell.le) _)
  have hsource : ∀ i k, k ≤ base → ∀ y ∈ tensorLocalSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (tensorLocalCoordinateExtension A (tensorLocalCoefficientField A b H i) i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_tensorLocalCoordinateExtension A (tensorLocalCoefficientField A b H i) i k (tensorLocalSampling_subset_target A i hy)]
    exact paperAtlasCj_model_native_jet_le c base (tensorLocalNativeCoordinates A b H)
      (fun i => (A.chart i).target) (tensorLocalSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (tensorLocalSampling_subset_target A)
      hH hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j + base → ∀ y ∈ tensorLocalInner A i,
      ‖iteratedFDeriv ℝ k (tensorLocalConvolution A mu K ell (tensorLocalCoefficientField A b H i) i) y‖ ≤ R := by
    intro i k hk y hy
    apply signedSmoothing_local_cumulative_gain mu hK hcompact
      (tensorLocalInner_open A i) (tensorLocalSamplingCoordinates_open A i)
      ((tensorLocalCoordinateExtension_contDiffOn A (tensorLocalCoefficientField A b H i) i (hH i)).mono (tensorLocalSampling_subset_target A i))
      hell hell1 _ base j P hP (hsource i) hk hy
    intro z hz w hw
    simpa only [one_smul] using tensorLocal_kernel_segment_mem_sampling A i hsupp hrho hell.le hell1 hz hw
      (s := 1) (by simp)
  let f := tensorLocalSmoothingCoordinates A mu K ell chi b H
  let O := fun i => (A.chart i).target
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    tensorLocalSmoothingCoordinates_contDiffOn A hA mu hK hcompact hsupp hrho hell.le hell1
      chi hchi hchiSupport b H hH hframe
  have hbound : ∀ p, ∀ k ≤ j + base, ∀ y ∈ (A.chart p).target,
      ‖iteratedFDeriv ℝ k (f p) y‖ ≤ tensorTransferConstant n B T J D (j + base) * R := by
    intro p k hk y hy
    exact tensorLocalSmoothingCoordinates_jet_le A hA mu hK hcompact hsupp hrho hell.le hell1 chi hchi hchiSupport
      b H hH hframe B T J hB hT hJ D p hy (hD _) (j + base) k hk R hR
      (fun i hi a => hweight p i a y hy hi)
      (fun i hi a ha => htransition p i a ha y hy hi)
      (fun i hi a r k => hframeBound p i a r k y hy hi)
      (fun i hi a ha => hlocal i a ha _ (tensorLocalInner_mem A i (hchiSupport i hi)))
  have hQR := mul_nonneg (tensorTransferConstant_nonneg n hB hT hJ D (j + base)) hR
  have hle := paperAtlasCj_model_le_of_native_bound c (j + base) f O (fun i => (A.chart i).target)
    (fun i => (A.chart i).open_target) (fun _ _ hy => hy) hf _ hQR hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal (mul_nonneg (linearModelFactor_nonneg _ _) hQR)] at hr
  change (paperAtlasCj (j + base) (modelCoordinateFamily c (tensorLocalSmoothingCoordinates A mu K ell chi b H))
      (tensorLocalModelTargets A c) (tensorLocalModelTargets A c)).toReal ≤ _ at hr
  apply hr.trans_eq
  unfold modelTensorTransferConstant
  dsimp only [R, P, I]
  ring

#print axioms round3Outer_paperAtlasCj_model_local_tensor_smoothing_gain

end
end GlobalEmbedding.Offline
