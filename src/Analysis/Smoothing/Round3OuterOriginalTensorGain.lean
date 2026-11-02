import Smoothing.TensorLocalOriginalGain
import Smoothing.Round3OuterOriginalTensor
import Smoothing.Round3OuterTensorWeightedGain
import Smoothing.TensorLocalOriginal
import Smoothing.TensorLocalWeightedGain

/-!
# Actual local-family tensor gain in the original coordinates

The output is a bilinear form on the original source tangent space at each
(p,x). The signed kernel, product atlas, source-first original coordinate ABI,
original chart-MAX norm, and actual fixed buffers are all retained. Frame
smoothness and bounds are derived from the actual joint chart Jacobian.
The parameter family need not cover P. The genuine C0 source budget is on
the fixed independent sampling buffers, not silently inferred from K alone.
-/

open Module MeasureTheory Manifold IsManifold GlobalEmbedding.Paper GlobalEmbedding.Continuation Function Set
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
  [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
  [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
  [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance round3Outer_tensorLocalOriginalGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round3Outer_tensorLocalOriginalGainManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M


/-- Every fixed slow norm of the SAME native parameterized tensor smoother
is controlled by the true original C0 tensor norm only. Full parameter
derivatives occur at positive slow order, with no parameter derivatives
silently added to the base norm. -/
theorem round3Outer_fixedKernel_original_local_parameter_tensor_smoothing_gain
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell : ℝ} (htau : 0 ≤ tau) (hell : 0 < ell) (htaul : tau ≤ ell) (hell1 : ell ≤ 1)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (H : (p : P) → (x : M) →
      LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i))
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k)
    (hfinite : paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤) :
    let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    let c := parameterTensorModelEquiv n d
    let K := fixedSmoothingKernel mu rho hrho r
    let S := tensorLocalParameterSmoothing A B hA mu K ell chi H
    let O := incrementsOriginalDifferentiation A B.chart
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart S i) (O i)) ∧
    paperAtlasWeighted 0 m tau (incrementsOriginalTensorCoordinates A B.chart S) O
      (incrementsOriginalDifferentiation A B.chart) ≠ ⊤ ∧
    (paperAtlasWeighted 0 m tau (incrementsOriginalTensorCoordinates A B.chart S) O
      (incrementsOriginalDifferentiation A B.chart)).toReal ≤
      modelTensorSmoothingGainConstant n c mu K Bc T (fun j => T (j + 1)) D 0 m *
        (paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
          O (tensorLocalOriginalSampling A B)).toReal := by
  dsimp only
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let c := parameterTensorModelEquiv n d
  let K := fixedSmoothingKernel mu rho hrho r
  let S := tensorLocalParameterSmoothing A B hA mu K ell chi H
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have hsource := tensorLocalNative_Cj_sampling_le_original A B hA H 0
  have hfiniteN := ne_top_of_le_ne_top hfinite hsource
  have h := round3Outer_paperAtlasWeighted_model_local_tensor_smoothing_gain (parameterLocalProductFamily A B) c
    (parameterLocalProductFamily_chart_mem A B hA hB) mu (K := K) hK.1 hK.2.1 hK.2.2.1 hbuffer
    hell hell1 htau htaul chi hchi hchiSupport (tensorLocalParameterFrame A B hA)
    (fun z => H z.1 z.2) (tensorLocalParameterInput_contDiffOn A B hA H hH)
    (tensorLocalParameterFrameTransition_contDiffOn A B hA)
    Bc T (fun j => T (j + 1)) hBc hT (fun j => hT (j + 1)) D hD hweight htransition
    (round3Outer_tensorLocalNativeFrame_bounds A B hA hB chi hchiSupport T htransition) 0 m hfiniteN
  have hS := tensorLocalParameterSmoothing_original_contDiffOn A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer hell.le hell1 chi hchi hchiSupport H hH
  have hEq := round3Outer_tensorLocalNative_weighted_allTargets_eq_original A B hA S 0 m tau
  change paperAtlasWeighted 0 m tau
    (modelCoordinateFamily c (tensorLocalSmoothingCoordinates (parameterLocalProductFamily A B) mu K ell chi
      (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2)))
    (tensorLocalModelTargets (parameterLocalProductFamily A B) c)
    (tensorLocalModelTargets (parameterLocalProductFamily A B) c) = _ at hEq
  dsimp only at h
  rw [hEq] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite hsource)
    (modelTensorSmoothingGainConstant_nonneg n c mu K hBc hT (fun j => hT (j + 1)) D 0 m)

#print axioms round3Outer_fixedKernel_original_local_parameter_tensor_smoothing_gain

end
end GlobalEmbedding.Offline
