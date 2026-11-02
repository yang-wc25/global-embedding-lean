import Smoothing.TensorParameterSmoothing

/-!
# Actual global tensor smoothing with finite parameters and original equation (6.4)

The output is a bilinear form on the original source tangent space at each
(p,x). The signed kernel, product atlas, source-first original coordinate ABI,
original chart-MAX norm, and actual fixed buffers are all retained. Frame
smoothness and bounds are derived from the actual joint chart Jacobian.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

/-- Every fixed slow norm of the SAME native parameterized tensor smoother
is controlled by the true original C0 tensor norm only. Full parameter
derivatives occur at positive slow order, with no parameter derivatives
silently added to the base norm. -/
theorem fixedKernel_original_parameter_tensor_smoothing_gain
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell : ℝ} (htau : 0 ≤ tau) (hell : 0 < ell) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i))
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ T k)
    (hfinite : paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤) :
    let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    let c := parameterTensorModelEquiv n d
    let K := fixedSmoothingKernel mu rho hrho r
    let S := parameterNativeTensorSmoothing A B hA mu K ell chi H
    let O := incrementsOriginalDifferentiation A B.chart
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart S i) (O i)) ∧
    paperAtlasWeighted 0 m tau (incrementsOriginalTensorCoordinates A B.chart S) O
      (parameterTensorOriginalInner A B) ≠ ⊤ ∧
    (paperAtlasWeighted 0 m tau (incrementsOriginalTensorCoordinates A B.chart S) O
      (parameterTensorOriginalInner A B)).toReal ≤
      modelTensorSmoothingGainConstant n c mu K Bc T (fun j => T (j + 1)) D 0 m *
        (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
          O (parameterTensorOriginalSampling A B)).toReal := by
  dsimp only
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let c := parameterTensorModelEquiv n d
  let K := fixedSmoothingKernel mu rho hrho r
  let S := parameterNativeTensorSmoothing A B hA mu K ell chi H
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have hsource := parameterTensor_Cj_sampling_le_original A B hA H 0
  have hfiniteN := ne_top_of_le_ne_top hfinite hsource
  have h := paperAtlasWeighted_model_tensor_smoothing_gain (parameterProductAtlas A B) c
    (parameterProductAtlas_smooth A B hA hB) mu (K := K) hK.1 hK.2.1 hK.2.2.1 hbuffer
    hell hell1 htau htaul chi hchi hchiSupport (parameterTensorNativeFrame A B hA)
    (fun z => H z.1 z.2) (parameterTensorNativeCoordinates_contDiffOn A B hA H hH)
    (parameterTensorNativeFrameTransition_contDiffOn A B hA hB)
    Bc T (fun j => T (j + 1)) hBc hT (fun j => hT (j + 1)) D hD hweight htransition
    (parameterNativeTensorFrame_bounds A B hA hB chi hchiSupport T htransition) 0 m hfiniteN
  have hS := parameterNativeTensorSmoothing_contDiffOn A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer hell.le hell1 chi hchi hchiSupport H hH
  have hEq := parameterTensor_weighted_inner_eq_original A B hA S 0 m tau
  change paperAtlasWeighted 0 m tau
    (modelCoordinateFamily c (bufferedTensorSmoothingCoordinates (parameterProductAtlas A B) mu K ell chi
      (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2)))
    (bufferedModelTargets (parameterProductAtlas A B) c)
    (bufferedModelInner (parameterProductAtlas A B) c) = _ at hEq
  dsimp only at h
  rw [hEq] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite hsource)
    (modelTensorSmoothingGainConstant_nonneg n c mu K hBc hT (fun j => hT (j + 1)) D 0 m)

end

end GlobalEmbedding.Offline
