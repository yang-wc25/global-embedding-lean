import Smoothing.Round3OuterDomains
import Smoothing.ParameterLocalMapWeightedGain
import Smoothing.Round3OuterMapGain
import GlobalEmbedding.Offline.BufferedWeightedGain

/-! Same actual smoother with receiving estimates on full chart targets.
Only active convolution centers require the original buffered inner charts.
The original constants, sampling buffers and native two-frame tensor formula
are unchanged. The old receiving-inner restriction is removed. -/

open GlobalEmbedding.Offline MeasureTheory GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Continuation

noncomputable section



variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d q : ℕ} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The SAME globally smoothed map has every fixed slow norm controlled by
only the original C^base source norm on its genuine fixed sampling buffers.
Output finiteness is established before taking its real value. -/
theorem round3Outer_paperAtlasWeighted_model_parameterLocalMap_smoothing_gain (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho tau ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho) (hrho : rho ≤ A.buffer)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u : M → Fin q → ℝ} (hu : ∀ i, ContDiffOn ℝ ∞ (u ∘ (A.chart i).symm) (A.chart i).target)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ (A.chart p).target,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (base m : ℕ) (hfinite : paperAtlasCj base (parameterLocalMapModelCoordinates A c u)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤) :
    let S := parameterLocalMapSmoothing A mu K ell chi u
    let f := parameterLocalMapModelCoordinates A c S
    let O := tensorLocalModelTargets A c
    paperAtlasWeighted base m tau f O (tensorLocalModelTargets A c) ≠ ⊤ ∧
      (paperAtlasWeighted base m tau f O (tensorLocalModelTargets A c)).toReal ≤
        modelBufferedSmoothingGainConstant c mu K B T D base m *
          (paperAtlasCj base (parameterLocalMapModelCoordinates A c u) O (tensorLocalModelSampling A c)).toReal := by
  dsimp only
  let f := parameterLocalMapModelCoordinates A c (parameterLocalMapSmoothing A mu K ell chi u)
  let O := tensorLocalModelTargets A c
  let U := tensorLocalModelTargets A c
  let I := (paperAtlasCj base (parameterLocalMapModelCoordinates A c u) O (tensorLocalModelSampling A c)).toReal
  let C := fun j => modelBufferedTransferConstant c B T D (j + base) *
    kernelGainConstant mu K j * nativeCoordinateFactor c base
  have hC : ∀ j, 0 ≤ C j := fun j => mul_nonneg
    (mul_nonneg (modelBufferedTransferConstant_nonneg c hB hT D _) (kernelGainConstant_nonneg mu K j))
    (nativeCoordinateFactor_nonneg c base)
  have hgain (j : ℕ) := round3Outer_paperAtlasCj_model_parameterLocalMap_smoothing_gain A c hA mu hK hcompact hsupp hrho
    hell hell1 chi hchi hchiSupport hu B T hB hT D hD hweight htransition base j hfinite
  have hs := parameterLocalMapSmoothing_contMDiff A hA mu hK hcompact hsupp hrho
    hell.le hell1 chi hchi hchiSupport u hu
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    modelCoordinateFamily_contDiffOn c (fun i =>
      (hs.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hA i))).contDiffOn)
  have hbdd := (paperAtlasCj_ne_top_iff (m + base) f O U (tensorLocalModelTargets_open A c)
    ((fun _ => Set.Subset.rfl)) hf).mp (hgain m).1
  have hout := paperAtlasWeighted_ne_top base m tau f O U (tensorLocalModelTargets_open A c)
    ((fun _ => Set.Subset.rfl)) hf hbdd
  refine ⟨hout, ?_⟩
  rw [paperAtlasWeighted_toReal base m tau htau _ O U hout]
  calc
    (∑ j ∈ Finset.range (m + 1), tau ^ j * (paperAtlasCj (j + base) f O U).toReal) ≤
        ∑ j ∈ Finset.range (m + 1), tau ^ j * (C j * (ell⁻¹)^j * I) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hgain j).2 (pow_nonneg htau _)
    _ = ∑ j ∈ Finset.range (m + 1), (C j * I) * (tau / ell)^j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_mul_inv, mul_pow]
      ring
    _ ≤ ∑ j ∈ Finset.range (m + 1), C j * I := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (mul_nonneg (hC j) ENNReal.toReal_nonneg)
        (pow_le_one₀ (div_nonneg htau hell.le) ((div_le_one hell).mpr htaul))
    _ = _ := by rw [← Finset.sum_mul]; rfl

#print axioms round3Outer_paperAtlasWeighted_model_parameterLocalMap_smoothing_gain
end

end GlobalEmbedding.Continuation
