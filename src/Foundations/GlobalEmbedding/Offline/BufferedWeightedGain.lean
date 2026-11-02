import GlobalEmbedding.Offline.BufferedSmoothingGain

/-!
# All fixed slow norms of the actual global smoother from the base norm

Source: `main.tex` 718–720, the assertion that every fixed smoothed slow norm
is controlled using only the genuine C2 map / C0 component source bounds.
The native global gain is summed in the ORIGINAL cumulative weighted norm.
For 0≤tau≤ell≤1, each actual factor tau^j ell^(-j) is at most one.
The constant is an explicit finite expression independent of the atlas size.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

section Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {d : ℕ}

/-- Explicit cost of all fixed-order slow norms of the same global smoother.
There is no atlas, manifold, chart-count, source, target-size, or scale argument. -/
def modelBufferedSmoothingGainConstant (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E)
    (K : E → ℝ) (B T : ℕ → ℝ) (D base m : ℕ) : ℝ :=
  ∑ j ∈ Finset.range (m + 1), modelBufferedTransferConstant c B T D (j + base) *
    kernelGainConstant mu K j * nativeCoordinateFactor c base

theorem modelBufferedSmoothingGainConstant_nonneg (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E)
    (K : E → ℝ) {B T : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D base m : ℕ) :
    0 ≤ modelBufferedSmoothingGainConstant c mu K B T D base m :=
  Finset.sum_nonneg fun j _ => mul_nonneg
    (mul_nonneg (modelBufferedTransferConstant_nonneg c hB hT D _) (kernelGainConstant_nonneg mu K j))
    (nativeCoordinateFactor_nonneg c base)

end Constants

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d q : ℕ} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The SAME globally smoothed map has every fixed slow norm controlled by
only the original C^base source norm on its genuine fixed sampling buffers.
Output finiteness is established before taking its real value. -/
theorem paperAtlasWeighted_model_buffered_smoothing_gain (A : BufferedAtlas M E)
    (c : E ≃L[ℝ] (Fin d → ℝ)) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure E) [mu.IsAddHaarMeasure]
    {K : E → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho tau ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho) (hrho : rho ≤ A.buffer)
    (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (base m : ℕ) (hfinite : paperAtlasCj base (bufferedModelCoordinates A c u)
      (bufferedModelTargets A c) (bufferedModelSampling A c) ≠ ⊤) :
    let S := bufferedSmoothing A mu K ell chi u
    let f := bufferedModelCoordinates A c S
    let O := bufferedModelTargets A c
    paperAtlasWeighted base m tau f O (bufferedModelInner A c) ≠ ⊤ ∧
      (paperAtlasWeighted base m tau f O (bufferedModelInner A c)).toReal ≤
        modelBufferedSmoothingGainConstant c mu K B T D base m *
          (paperAtlasCj base (bufferedModelCoordinates A c u) O (bufferedModelSampling A c)).toReal := by
  dsimp only
  let f := bufferedModelCoordinates A c (bufferedSmoothing A mu K ell chi u)
  let O := bufferedModelTargets A c
  let U := bufferedModelInner A c
  let I := (paperAtlasCj base (bufferedModelCoordinates A c u) O (bufferedModelSampling A c)).toReal
  let C := fun j => modelBufferedTransferConstant c B T D (j + base) *
    kernelGainConstant mu K j * nativeCoordinateFactor c base
  have hC : ∀ j, 0 ≤ C j := fun j => mul_nonneg
    (mul_nonneg (modelBufferedTransferConstant_nonneg c hB hT D _) (kernelGainConstant_nonneg mu K j))
    (nativeCoordinateFactor_nonneg c base)
  have hgain (j : ℕ) := paperAtlasCj_model_buffered_smoothing_gain A c hA mu hK hcompact hsupp hrho
    hell hell1 chi hchi hchiSupport hu B T hB hT D hD hweight htransition base j hfinite
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) :=
    bufferedModelCoordinates_contDiffOn A hA c
      (bufferedSmoothing_contMDiff A hA mu hK hcompact hsupp hrho hell.le hell1 chi hchi hchiSupport hu)
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
