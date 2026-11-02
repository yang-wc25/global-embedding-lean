import Smoothing.ParameterOriginalSmoothing
import Smoothing.IntegrationParameterWeightedGain

/-!
# Gain for the same fixed global parameter-map smoothing operator

The input is the actual original spatial C2 norm with joint order zero.
Every weighted joint order m is controlled for 0 <= tau <= ell <= 1.
The finite global parameter-atlas scope is exactly the tail theorem's scope.
This anisotropic gain is separate from the frozen total-joint base-two gain
proved in ParameterTotalGain; the two input norms are not identified.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d q : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterOriginalGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterOriginalGainIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)
local notation "cp" => EuclideanSpace.equiv (Fin d) ℝ
local notation "cs" => EuclideanSpace.equiv (Fin n) ℝ
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ

/-- Actual original-ABI weighted gain from the original spatial C2 input.
It uses the same kernel of order r as the original (6.4) tail for every m. -/
theorem fixedKernel_original_parameter_map_smoothing_gain
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    {u : P × M → Ey} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) 0 (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let C := parameterSpatialTransferCoefficient Es Ey Bc T
    let S := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
    let O := incrementsOriginalDifferentiation A B.chart
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ S ∧
    parameterSpatialWeighted (n := n) (d := d) m tau
      (incrementsOriginalMapCoordinates A B.chart S) O (parameterTensorOriginalInner A B) ≠ ⊤ ∧
    (parameterSpatialWeighted (n := n) (d := d) m tau
      (incrementsOriginalMapCoordinates A B.chart S) O (parameterTensorOriginalInner A B)).toReal ≤
      parameterModelSmoothingGainConstant cp cs cy mu K C T D m *
        (parameterSpatialCj (n := n) (d := d) 0
          (incrementsOriginalMapCoordinates A B.chart u) O (parameterTensorOriginalSampling A B)).toReal := by
  dsimp only
  let mu := (volume : Measure (Ep × Es))
  let K := fixedSmoothingKernel mu rho hrho r
  let S := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
  let C := parameterSpatialTransferCoefficient Es Ey Bc T
  have hC := parameterSpatialTransferCoefficient_nonneg Es Ey hBc hT
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have hNLe := parameterMap_Cj_sampling_le_original A B u 0
  have hNN := ne_top_of_le_ne_top hfinite hNLe
  have hc := parameterBufferedTransfer_bound_of_providers (Y := Ey) A B hA hB chi hchi
    hchiSupport Bc T hBc hT hweight htransition
  have h := parameterBufferedSmoothing_original_weighted_gain A B hA hB cp cs cy mu
    hK.1 hK.2.1 m hK.2.2.1 hbuffer hell hell1 htau htaul chi hchi
    hchiSupport hu C T hC hT D hD hc htransition hNN
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer hell.le hell1 chi hchi hchiSupport hu
  have hEq := parameterMap_weighted_inner_eq_original A B S m tau
  dsimp only at h
  dsimp only [S, K] at hEq
  rw [hEq] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite hNLe)
    (parameterModelSmoothingGainConstant_nonneg cp cs cy mu K hC hT D m)

#print axioms fixedKernel_original_parameter_map_smoothing_gain
end
end GlobalEmbedding.Continuation
