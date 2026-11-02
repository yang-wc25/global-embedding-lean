import Smoothing.Round3OuterDomains
import Smoothing.TensorLocalWeightedGain
import Smoothing.Round3OuterTensorGain

/-! Same actual smoother with receiving estimates on full chart targets.
Only active convolution centers require the original buffered inner charts.
The original constants, sampling buffers and native two-frame tensor formula
are unchanged. The old receiving-inner restriction is removed. -/

open Module MeasureTheory GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false



variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d n : ℕ} {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The SAME globally smoothed tensor has every fixed slow norm controlled by
only the original C^base source norm on its genuine fixed sampling buffers.
Output finiteness is established before taking its real value. -/
theorem round3Outer_paperAtlasWeighted_model_local_tensor_smoothing_gain (A : TensorBufferedChartFamily ι M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho tau ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho) (hrho : rho ≤ A.buffer)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : ι → M → ℝ)
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
    (base m : ℕ) (hfinite : paperAtlasCj base (tensorLocalModelCoordinates A c b H)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤) :
    let f := modelCoordinateFamily c (tensorLocalSmoothingCoordinates A mu K ell chi b H)
    let O := tensorLocalModelTargets A c
    paperAtlasWeighted base m tau f O (tensorLocalModelTargets A c) ≠ ⊤ ∧
      (paperAtlasWeighted base m tau f O (tensorLocalModelTargets A c)).toReal ≤
        modelTensorSmoothingGainConstant n c mu K B T J D base m *
          (paperAtlasCj base (tensorLocalModelCoordinates A c b H) O (tensorLocalModelSampling A c)).toReal := by
  dsimp only
  let f := modelCoordinateFamily c (tensorLocalSmoothingCoordinates A mu K ell chi b H)
  let O := tensorLocalModelTargets A c
  let U := tensorLocalModelTargets A c
  let I := (paperAtlasCj base (tensorLocalModelCoordinates A c b H) O (tensorLocalModelSampling A c)).toReal
  let C := fun j => modelTensorTransferConstant n c B T J D (j + base) *
    kernelGainConstant mu K j * nativeCoordinateFactor c base
  have hC : ∀ j, 0 ≤ C j := fun j => mul_nonneg
    (mul_nonneg (modelTensorTransferConstant_nonneg n c hB hT hJ D _) (kernelGainConstant_nonneg mu K j))
    (nativeCoordinateFactor_nonneg c base)
  have hgain (j : ℕ) := round3Outer_paperAtlasCj_model_local_tensor_smoothing_gain A c hA mu hK hcompact hsupp hrho
    hell hell1 chi hchi hchiSupport b H hH hframe B T J hB hT hJ D hD hweight htransition hframeBound base j hfinite
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    modelCoordinateFamily_contDiffOn c
      (tensorLocalSmoothingCoordinates_contDiffOn A hA mu hK hcompact hsupp hrho hell.le hell1
        chi hchi hchiSupport b H hH hframe)
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

#print axioms round3Outer_paperAtlasWeighted_model_local_tensor_smoothing_gain

end
end GlobalEmbedding.Offline
