import Smoothing.TensorGain

/-!
# All fixed slow norms of the actual global smoother from the base norm

Source: `main.tex` 718–720, the assertion that every fixed smoothed slow norm
is controlled using only the genuine C0 tensor source bounds.
The native global gain is summed in the ORIGINAL cumulative weighted norm.
For 0≤tau≤ell≤1, each actual factor tau^j ell^(-j) is at most one.
The constant is an explicit finite expression independent of the atlas size.
-/

open Module MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

section Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {d : ℕ}

/-- Explicit cost of all fixed-order slow norms of the same global smoother.
There is no atlas, manifold, chart-count, source, or scale argument. -/
def modelTensorSmoothingGainConstant (n : ℕ) (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E)
    (K : E → ℝ) (B T J : ℕ → ℝ) (D base m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), modelTensorTransferConstant n c B T J D (j + base) *
    kernelGainConstant mu K j * nativeCoordinateFactor c base

theorem modelTensorSmoothingGainConstant_nonneg (n : ℕ) (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E)
    (K : E → ℝ) {B T J : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j) (D base m : ℕ) :
    0 ≤ modelTensorSmoothingGainConstant n c mu K B T J D base m :=
  Finset.sum_nonneg fun j _ => mul_nonneg
    (mul_nonneg (modelTensorTransferConstant_nonneg n c hB hT hJ D _) (kernelGainConstant_nonneg mu K j))
    (nativeCoordinateFactor_nonneg c base)

end Constants

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d n : ℕ} {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The SAME globally smoothed tensor has every fixed slow norm controlled by
only the original C^base source norm on its genuine fixed sampling buffers.
Output finiteness is established before taking its real value. -/
theorem paperAtlasWeighted_model_tensor_smoothing_gain (A : BufferedAtlas M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho tau ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho) (hrho : rho ≤ A.buffer)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : Fin A.count → M → ℝ)
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
    (base m : ℕ) (hfinite : paperAtlasCj base (bufferedTensorModelCoordinates A c b H)
      (bufferedModelTargets A c) (bufferedModelSampling A c) ≠ ⊤) :
    let f := modelCoordinateFamily c (bufferedTensorSmoothingCoordinates A mu K ell chi b H)
    let O := bufferedModelTargets A c
    paperAtlasWeighted base m tau f O (bufferedModelInner A c) ≠ ⊤ ∧
      (paperAtlasWeighted base m tau f O (bufferedModelInner A c)).toReal ≤
        modelTensorSmoothingGainConstant n c mu K B T J D base m *
          (paperAtlasCj base (bufferedTensorModelCoordinates A c b H) O (bufferedModelSampling A c)).toReal := by
  dsimp only
  let f := modelCoordinateFamily c (bufferedTensorSmoothingCoordinates A mu K ell chi b H)
  let O := bufferedModelTargets A c
  let U := bufferedModelInner A c
  let I := (paperAtlasCj base (bufferedTensorModelCoordinates A c b H) O (bufferedModelSampling A c)).toReal
  let C := fun j => modelTensorTransferConstant n c B T J D (j + base) *
    kernelGainConstant mu K j * nativeCoordinateFactor c base
  have hC : ∀ j, 0 ≤ C j := fun j => mul_nonneg
    (mul_nonneg (modelTensorTransferConstant_nonneg n c hB hT hJ D _) (kernelGainConstant_nonneg mu K j))
    (nativeCoordinateFactor_nonneg c base)
  have hgain (j : ℕ) := paperAtlasCj_model_tensor_smoothing_gain A c hA mu hK hcompact hsupp hrho
    hell hell1 chi hchi hchiSupport b H hH hframe B T J hB hT hJ D hD hweight htransition hframeBound base j hfinite
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    modelCoordinateFamily_contDiffOn c
      (bufferedTensorSmoothingCoordinates_contDiffOn A hA mu hK hcompact hsupp hrho hell.le hell1
        chi hchi hchiSupport b H hH hframe)
  have hbdd := (paperAtlasCj_ne_top_iff (m + base) f O U (bufferedModelTargets_open A c)
    (bufferedModelInner_subset_target A c) hf).mp (hgain m).1
  have hout := paperAtlasWeighted_ne_top base m tau f O U (bufferedModelTargets_open A c)
    (bufferedModelInner_subset_target A c) hf hbdd
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

end

end GlobalEmbedding.Offline
