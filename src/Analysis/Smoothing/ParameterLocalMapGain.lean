import Smoothing.ParameterLocalMapGainJets
import Smoothing.ParameterLocalMapEstimates
import GlobalEmbedding.Offline.LocalKernelGain

/-!
# Actual local-family derivative gain from the true low-order source norm

Source: `main.tex` 700–720, gain from the genuine C2 map / C0 component input.
The same global smoother is localized using its actual cutoff and chart
transition derivatives. Local gain uses a bounded indicator only to prove
local integrability; neighborhood equality returns every derivative to the
original operator. The final norm is the frozen original cumulative chart
maximum, on actual component coordinates of the original source model.
No compact support or global integrability of the original source is assumed.
The family need not cover the manifold and no partition identity is needed
for gain. Proof port: the existing BufferedSmoothingGain estimate, using the
same local kernel theorem and actual cover-free map smoothing.
-/

open GlobalEmbedding.Offline MeasureTheory GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff Topology ENNReal

namespace GlobalEmbedding.Continuation

noncomputable section

variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d q : ℕ} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual global cumulative C^(j+base) bound costs only ell^-j times
the true original C^base source bound. The source norm is evaluated on fixed
sampling buffers; the output norm is on original inner domains. Every native
cutoff/transition term and the actual support multiplicity is included. -/
theorem paperAtlasCj_model_parameterLocalMap_smoothing_gain (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho) (hrho : rho ≤ A.buffer)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u : M → Fin q → ℝ} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ tensorLocalInner A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ tensorLocalInner A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (base j : ℕ) (hfinite : paperAtlasCj base (parameterLocalMapModelCoordinates A c u)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤) :
    let S := parameterLocalMapSmoothing A mu K ell chi u
    let f := parameterLocalMapModelCoordinates A c S
    let O := tensorLocalModelTargets A c
    paperAtlasCj (j + base) f O (tensorLocalModelInner A c) ≠ ⊤ ∧
      (paperAtlasCj (j + base) f O (tensorLocalModelInner A c)).toReal ≤
        (modelBufferedTransferConstant c B T D (j + base) * kernelGainConstant mu K j *
          nativeCoordinateFactor c base) * (ell⁻¹)^j *
          (paperAtlasCj base (parameterLocalMapModelCoordinates A c u) O (tensorLocalModelSampling A c)).toReal := by
  dsimp only
  let I := (paperAtlasCj base (parameterLocalMapModelCoordinates A c u)
    (tensorLocalModelTargets A c) (tensorLocalModelSampling A c)).toReal
  let P := nativeCoordinateFactor c base * I
  let R := kernelGainConstant mu K j * P * (ell⁻¹)^j
  have hP : 0 ≤ P := mul_nonneg (nativeCoordinateFactor_nonneg c base) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelGainConstant_nonneg mu K j) hP)
    (pow_nonneg (inv_nonneg.mpr hell.le) _)
  have hsource : ∀ i k, k ≤ base → ∀ y ∈ tensorLocalSamplingCoordinates A i,
      ‖iteratedFDeriv ℝ k (tensorLocalCoordinateExtension A u i) y‖ ≤ P := by
    intro i k hk y hy
    rw [iteratedFDeriv_tensorLocalCoordinateExtension A u i k (tensorLocalSampling_subset_target A i hy)]
    exact paperAtlasCj_model_native_jet_le c base (parameterLocalMapNativeCoordinates A u)
      (fun i => (A.chart i).target) (tensorLocalSamplingCoordinates A)
      (fun i => (A.chart i).open_target) (tensorLocalSampling_subset_target A)
      hu hfinite i hk hy
  have hlocal : ∀ i k, k ≤ j + base → ∀ y ∈ tensorLocalInner A i,
      ‖iteratedFDeriv ℝ k (tensorLocalConvolution A mu K ell u i) y‖ ≤ R := by
    intro i k hk y hy
    apply signedSmoothing_local_cumulative_gain mu hK hcompact
      (tensorLocalInner_open A i) (tensorLocalSamplingCoordinates_open A i)
      ((tensorLocalCoordinateExtension_contDiffOn A u i (hu i)).mono (tensorLocalSampling_subset_target A i))
      hell hell1 _ base j P hP (hsource i) hk hy
    intro z hz w hw
    simpa only [one_smul] using tensorLocal_kernel_segment_mem_sampling A i hsupp hrho hell.le hell1 hz hw
      (s := 1) (by simp)
  let f := parameterLocalMapNativeCoordinates A (parameterLocalMapSmoothing A mu K ell chi u)
  let O := fun i => (A.chart i).target
  have hs := parameterLocalMapSmoothing_contMDiff A hA mu hK hcompact hsupp hrho
    hell.le hell1 chi hchi hchiSupport u hu
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) := by
    intro i
    exact (hs.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA i))).contDiffOn
  have hbound : ∀ p, ∀ k ≤ j + base, ∀ y ∈ tensorLocalInner A p,
      ‖iteratedFDeriv ℝ k (f p) y‖ ≤ bufferedTransferConstant B T D (j + base) * R := by
    intro p k hk y hy
    exact parameterLocalMapSmoothing_gain_chart_jet_le A hA mu hK hcompact hsupp hrho hell.le hell1 chi hchi hchiSupport
      hu B T hB hT D p hy.1 (hD _) (j + base) k hk R hR
      (fun i hi a => hweight p i a y hy hi)
      (fun i hi a ha => htransition p i a ha y hy hi)
      (fun i hi a ha => hlocal i a ha _ (tensorLocalInner_mem A i (hchiSupport i hi)))
  have hQR := mul_nonneg (bufferedTransferConstant_nonneg hB hT D (j + base)) hR
  have hle := paperAtlasCj_model_le_of_native_bound c (j + base) f O (tensorLocalInner A)
    (fun i => (A.chart i).open_target) (fun _ _ hy => hy.1) hf _ hQR hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hr := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal (mul_nonneg (linearModelFactor_nonneg _ _) hQR)] at hr
  change (paperAtlasCj (j + base) (parameterLocalMapModelCoordinates A c (parameterLocalMapSmoothing A mu K ell chi u))
      (tensorLocalModelTargets A c) (tensorLocalModelInner A c)).toReal ≤ _ at hr
  apply hr.trans_eq
  unfold modelBufferedTransferConstant
  dsimp only [R, P, I]
  ring

#print axioms paperAtlasCj_model_parameterLocalMap_smoothing_gain
end

end GlobalEmbedding.Continuation
