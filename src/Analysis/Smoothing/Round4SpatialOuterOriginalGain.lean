import Smoothing.Round4SpatialOuterOriginalTail
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
set_option backward.isDefEq.respectTransparency false

variable {n d q : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance round4SpatialOriginalGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
private local instance round4SpatialOriginalGainIsManifold : IsManifold
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
theorem round4SpatialOuter_original_map_gain
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (R : Fin A.count × Fin B.count → Set (Fin (n+d) → ℝ))
    (hR : ∀ i, R i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    {u : P × M → Ey} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ ((parameterProductAtlas A B).chart p).target,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterProductAtlas A B).chart p).target,
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
      (incrementsOriginalMapCoordinates A B.chart S) O R ≠ ⊤ ∧
    (parameterSpatialWeighted (n := n) (d := d) m tau
      (incrementsOriginalMapCoordinates A B.chart S) O R).toReal ≤
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
  have hc : ∀ p i k, ∀ z ∈ ((parameterProductAtlas A B).chart p).target,
      ((parameterProductAtlas A B).chart p).symm z ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Ey) A B chi p i) z‖ ≤ C k := by
    intro p i k z hz hi
    exact parameterBufferedTransfer_jet_le A B hA hB chi hchi Bc T hBc hT p i
      ⟨hz,hchiSupport i hi⟩ k (fun a _ => hweight p i a z hz hi)
      (fun a ha _ => htransition p i a ha z hz hi)
  have h := round4SpatialOuter_original_weighted_gain A B (round4SpatialOriginalNativeOutput A B R)
    (round4SpatialOriginalNativeOutput_subset A B R hR) hA hB cp cs cy mu
    hK.1 hK.2.1 m hK.2.2.1 hbuffer hell hell1 htau htaul chi hchi
    hchiSupport hu C T hC hT D hD hc htransition hNN
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer hell.le hell1 chi hchi hchiSupport hu
  have hEq := round4SpatialOriginalOutput_weighted_eq A B S m tau R
  dsimp only at h
  dsimp only [S, K] at hEq
  rw [hEq] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite hNLe)
    (parameterModelSmoothingGainConstant_nonneg cp cs cy mu K hC hT D m)

#print axioms GlobalEmbedding.Continuation.round4SpatialOuter_original_map_gain
end
end GlobalEmbedding.Continuation
