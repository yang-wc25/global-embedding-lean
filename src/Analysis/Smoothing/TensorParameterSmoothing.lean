import Smoothing.TensorParameterNorms
import Smoothing.TensorWeighted
import Smoothing.TensorWeightedGain
import Smoothing.TensorLinearity
import GlobalEmbedding.Offline.FixedSmoothingKernel
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

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

/-- The actual native parameterized tensor smoother, with source tangent slots. -/
def parameterNativeTensorSmoothing
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → ℝ)
    (ell : ℝ) (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (p : P) (x : M) : LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x) :=
  bufferedTensorSmoothing (parameterProductAtlas A B) mu K ell chi
    (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2) (p, x)

theorem parameterNativeTensorSmoothing_isSymm
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d))) (hA : IsSmoothBufferedAtlas A)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    (K : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → ℝ)
    (ell : ℝ) (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ p x, (H p x).IsSymm) (p : P) (x : M) :
    (parameterNativeTensorSmoothing A B hA mu K ell chi H p x).IsSymm :=
  bufferedTensorSmoothing_isSymm _ mu K ell chi _ _ (fun z => hH z.1 z.2) (p, x)

/-- Original joint tensor coefficient smoothness of the same actual output. -/
theorem parameterNativeTensorSmoothing_contDiffOn
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (mu : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))) [mu.IsAddHaarMeasure]
    {K : EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n) → ℝ}
    (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i)) (i : Fin A.count × Fin B.count) :
    ContDiffOn ℝ ∞
      (incrementsOriginalTensorCoordinates A B.chart (parameterNativeTensorSmoothing A B hA mu K ell chi H) i)
      (incrementsOriginalDifferentiation A B.chart i) := by
  apply parameterTensorOriginalCoordinates_contDiffOn A B hA
  exact bufferedTensorSmoothingCoordinates_contDiffOn (parameterProductAtlas A B)
    (parameterProductAtlas_smooth A B hA hB) mu hK hcompact hsupp hrho hell hell1
    chi hchi hchiSupport (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2)
    (parameterTensorNativeCoordinates_contDiffOn A B hA H hH)
    (parameterTensorNativeFrameTransition_contDiffOn A B hA hB)

/-- Original joint transition bounds supply every required tensor frame
bound with one extra derivative and no independent frame provider. -/
theorem parameterNativeTensorFrame_bounds
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    (T : ℕ → ℝ)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ T k) :
    ∀ p i a r k, ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k
        (tensorFrameTransition (parameterProductAtlas A B) (parameterTensorNativeFrame A B hA) p i a r) y‖ ≤ T (k + 1) := by
  intro p i a r k y hy hi
  exact (parameterTensorNativeFrameTransition_jet_le A B hA hB p i a r
    ⟨hy.1, hchiSupport i hi⟩ k).trans (htransition p i (k + 1) (by omega) y hy hi)

/-- Tensor half of original (6.4), on the actual native field over arbitrary
finite-dimensional parameters. The only geometric derivative providers are
the original cutoff and joint chart transition bounds. Signed smoothing is
not assumed to preserve positivity. -/
theorem fixedKernel_original_parameter_tensor_smoothing_tail
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : BufferedAtlas P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
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
    (hNr : paperAtlasWeighted 0 r t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤)
    (hNm : paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 0 r t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    let c := parameterTensorModelEquiv n d
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let S := parameterNativeTensorSmoothing A B hA mu K ell chi H
    let O := incrementsOriginalDifferentiation A B.chart
    let e := incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x - S p x)
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart S i) (O i)) ∧
    paperAtlasWeighted 0 m tau e O (parameterTensorOriginalInner A B) ≠ ⊤ ∧
    (paperAtlasWeighted 0 m tau e O (parameterTensorOriginalInner A B)).toReal ≤
      modelTensorSmoothingTailConstant n c mu kappa Bc T (fun j => T (j + 1)) D 0 m r *
        (budget * (ell / t) ^ r + (paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H)
          O (parameterTensorOriginalSampling A B)).toReal * (tau / t) ^ r) := by
  dsimp only
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let c := parameterTensorModelEquiv n d
  let K := fixedSmoothingKernel mu rho hrho r
  let S := parameterNativeTensorSmoothing A B hA mu K ell chi H
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hb := normalizedSmoothingBase_spec mu rho hrho
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have hNrLe := parameterTensor_weighted_sampling_le_original A B hA H 0 r t
  have hNmLe := parameterTensor_weighted_sampling_le_original A B hA H 0 m t
  have hNrN := ne_top_of_le_ne_top hNr hNrLe
  have hNmN := ne_top_of_le_ne_top hNm hNmLe
  have hbudgetN := (ENNReal.toReal_mono hNr hNrLe).trans hbudget
  have h := paperAtlasWeighted_model_tensor_smoothing_tail (parameterProductAtlas A B) c
    (parameterProductAtlas_smooth A B hA hB) mu hb.1 hb.2.1 hb.2.2.1 0 m r hK.2.2.1 hbuffer
    htau htaul helt ht1 chi hchi hchiSupport hpartition (parameterTensorNativeFrame A B hA)
    (fun z => H z.1 z.2) (parameterTensorNativeCoordinates_contDiffOn A B hA H hH)
    (parameterTensorNativeFrameTransition_contDiffOn A B hA hB)
    Bc T (fun j => T (j + 1)) hBc hT (fun j => hT (j + 1)) D hD hweight htransition
    (parameterNativeTensorFrame_bounds A B hA hB chi hchiSupport T htransition)
    hNrN hNmN budget hbudgetN
  have hS := parameterNativeTensorSmoothing_contDiffOn A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport H hH
  have hEq := parameterTensor_weighted_inner_eq_original A B hA (fun p x => S p x - H p x) 0 m tau
  change paperAtlasWeighted 0 m tau
    (modelCoordinateFamily c (bufferedTensorErrorCoordinates (parameterProductAtlas A B) mu K ell chi
      (parameterTensorNativeFrame A B hA) (fun z => H z.1 z.2)))
    (bufferedModelTargets (parameterProductAtlas A B) c)
    (bufferedModelInner (parameterProductAtlas A B) c) = _ at hEq
  dsimp only at h
  dsimp only [K, fixedSmoothingKernel] at hEq
  rw [hEq] at h
  have hO : ∀ i, IsOpen (incrementsOriginalDifferentiation A B.chart i) := by
    intro i
    rw [← parameterTensorModel_targets A B i]
    exact bufferedModelTargets_open _ _ _
  have hcomm := paperAtlasWeighted_sub_comm 0 m tau
    (incrementsOriginalTensorCoordinates A B.chart H) (incrementsOriginalTensorCoordinates A B.chart S)
    (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalInner A B) hO
    (parameterTensorOriginalInner_subset A B) hH hS
  change paperAtlasWeighted 0 m tau
    (incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x - S p x)) _ _ =
    paperAtlasWeighted 0 m tau
    (incrementsOriginalTensorCoordinates A B.chart (fun p x => S p x - H p x)) _ _ at hcomm
  rw [← hcomm] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _
    (modelTensorSmoothingTailConstant_nonneg n c mu _ hBc hT (fun j => hT (j + 1)) D 0 m r)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hNm hNmLe)
    (pow_nonneg (div_nonneg htau.le ((htau.trans_le htaul).trans_le helt).le) _)

end

end GlobalEmbedding.Offline
