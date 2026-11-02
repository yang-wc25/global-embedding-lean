import Smoothing.Round3OuterOriginalDomains
import Smoothing.Round3OuterTensorWeighted
import Smoothing.TensorLocalNative

/-!
Original equation (6.4) for the actual source-tangent tensor with parameter
charts covering only an open neighborhood of K. Every geometric derivative
provider is a true cutoff or transition jet; frame bounds are derived.

The source norm uses fixed independent source/parameter sampling buffers,
with parameterSet=univ. This controls only those explicit buffer domains;
it is not inferred from the frozen Core budget restricted to K. A bridge
from that original input-control region remains a separate obligation.
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

local instance round3Outer_tensorLocalOriginalChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round3Outer_tensorLocalOriginalManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M


/-- Original joint transition bounds supply every required tensor frame
bound with one extra derivative and no independent frame provider. -/
theorem round3Outer_tensorLocalNativeFrame_bounds
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (T : ℕ → ℝ)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k) :
    ∀ p i a r k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k
        (tensorLocalFrameTransition (parameterLocalProductFamily A B) (tensorLocalParameterFrame A B hA) p i a r) y‖ ≤ T (k + 1) := by
  intro p i a r k y hy hi
  exact (tensorLocalNativeFrame_jet_le A B hA hB p i a r
    ⟨hy, hchiSupport i hi⟩ k).trans (htransition p i (k + 1) (by omega) y hy hi)

/-- Tensor half of original (6.4), on the actual native field over arbitrary
finite-dimensional parameters. The only geometric derivative providers are
the original cutoff and joint chart transition bounds. Signed smoothing is
not assumed to preserve positivity. -/
theorem round3Outer_fixedKernel_original_local_parameter_tensor_smoothing_tail
    (A : BufferedAtlas M (EuclideanSpace ℝ (Fin n)))
    (B : TensorBufferedChartFamily (Fin pcount) P (EuclideanSpace ℝ (Fin d)))
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n))
      𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (W : Set P) (hW : IsOpen W) (hpartition : ∀ z : P × M, z.1 ∈ W → ∑ i, chi i z ^ 2 = 1)
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
    (hNr : paperAtlasWeighted 0 r t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (hNm : paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 0 r t (incrementsOriginalTensorCoordinates A B.chart H)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
    let c := parameterTensorModelEquiv n d
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let S := tensorLocalParameterSmoothing A B hA mu K ell chi H
    let O := incrementsOriginalDifferentiation A B.chart
    let e := incrementsOriginalTensorCoordinates A B.chart (fun p x => H p x - S p x)
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart S i) (O i)) ∧
    paperAtlasWeighted 0 m tau e O (round3OuterOriginalEvaluation A B W) ≠ ⊤ ∧
    (paperAtlasWeighted 0 m tau e O (round3OuterOriginalEvaluation A B W)).toReal ≤
      modelTensorSmoothingTailConstant n c mu kappa Bc T (fun j => T (j + 1)) D 0 m r *
        (budget * (ell / t) ^ r + (paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H)
          O (tensorLocalOriginalSampling A B)).toReal * (tau / t) ^ r) := by
  dsimp only
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let c := parameterTensorModelEquiv n d
  let K := fixedSmoothingKernel mu rho hrho r
  let S := tensorLocalParameterSmoothing A B hA mu K ell chi H
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hb := normalizedSmoothingBase_spec mu rho hrho
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have hNrLe := tensorLocalNative_weighted_sampling_le_original A B hA H 0 r t
  have hNmLe := tensorLocalNative_weighted_sampling_le_original A B hA H 0 m t
  have hNrN := ne_top_of_le_ne_top hNr hNrLe
  have hNmN := ne_top_of_le_ne_top hNm hNmLe
  have hbudgetN := (ENNReal.toReal_mono hNr hNrLe).trans hbudget
  have h := round3Outer_paperAtlasWeighted_model_local_tensor_smoothing_tail (parameterLocalProductFamily A B) c
    (parameterLocalProductFamily_chart_mem A B hA hB) mu hb.1 hb.2.1 hb.2.2.1 0 m r hK.2.2.1 hbuffer
    htau htaul helt ht1 chi hchi hchiSupport (Prod.fst ⁻¹' W) (hW.preimage continuous_fst) hpartition (tensorLocalParameterFrame A B hA)
    (fun z => H z.1 z.2) (tensorLocalParameterInput_contDiffOn A B hA H hH)
    (tensorLocalParameterFrameTransition_contDiffOn A B hA)
    Bc T (fun j => T (j + 1)) hBc hT (fun j => hT (j + 1)) D hD hweight htransition
    (round3Outer_tensorLocalNativeFrame_bounds A B hA hB chi hchiSupport T htransition)
    hNrN hNmN budget hbudgetN
  have hS := tensorLocalParameterSmoothing_original_contDiffOn A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport H hH
  have hEq := round3Outer_tensorLocalNative_weighted_eq_original A B hA (fun p x => S p x - H p x) W 0 m tau
  change paperAtlasWeighted 0 m tau
    (modelCoordinateFamily c (tensorLocalErrorCoordinates (parameterLocalProductFamily A B) mu K ell chi
      (tensorLocalParameterFrame A B hA) (fun z => H z.1 z.2)))
    (tensorLocalModelTargets (parameterLocalProductFamily A B) c)
    (round3OuterModelEvaluation (parameterLocalProductFamily A B) c (Prod.fst ⁻¹' W)) = _ at hEq
  dsimp only at h
  dsimp only [K, fixedSmoothingKernel] at hEq
  rw [hEq] at h
  have hO : ∀ i, IsOpen (incrementsOriginalDifferentiation A B.chart i) := by
    intro i
    rw [← parameterLocalProduct_targets A B i]
    exact tensorLocalModelTargets_open _ _ _
  have hcomm := paperAtlasWeighted_sub_comm 0 m tau
    (incrementsOriginalTensorCoordinates A B.chart H) (incrementsOriginalTensorCoordinates A B.chart S)
    (incrementsOriginalDifferentiation A B.chart) (round3OuterOriginalEvaluation A B W) hO
    (round3OuterOriginalEvaluation_subset A B W) hH hS
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

#print axioms round3Outer_fixedKernel_original_local_parameter_tensor_smoothing_tail

end
end GlobalEmbedding.Offline
