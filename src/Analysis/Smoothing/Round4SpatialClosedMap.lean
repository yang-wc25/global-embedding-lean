import Smoothing.Round4SpatialOuterOriginalGain
import Smoothing.Round4SpatialClosedProviders
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

variable {n d q pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance round4SpatialClosedMapChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
private local instance round4SpatialClosedMapIsManifold : IsManifold
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

theorem round4SpatialClosed_actual_map_tail
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i)
    (R : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hR : ∀ i, R i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Ey} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k)
    (hNr : parameterSpatialWeighted (n := n) (d := d) r t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (hNm : parameterSpatialWeighted (n := n) (d := d) m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget : (parameterSpatialWeighted (n := n) (d := d) r t
      (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
      (tensorLocalOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let C := parameterSpatialTransferCoefficient Es Ey Bc T
    let S := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
    let O := incrementsOriginalDifferentiation A B.chart
    let e := incrementsOriginalMapCoordinates A B.chart (fun z => u z - S z)
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ S ∧
    parameterSpatialWeighted (n := n) (d := d) m tau e O R ≠ ⊤ ∧
    (parameterSpatialWeighted (n := n) (d := d) m tau e O R).toReal ≤
      parameterModelSmoothingTailConstant cp cs cy mu kappa C T D m r *
        (budget * (ell / t) ^ r + (parameterSpatialWeighted (n := n) (d := d) m t
          (incrementsOriginalMapCoordinates A B.chart u) O
          (tensorLocalOriginalSampling A B)).toReal * (tau / t) ^ r) := by
  let B' := round4ClosedParameterAtlas B hcover
  let chi' := fun k => chi ((parameterTensorAtlasIndex A B').symm k)
  have hB' := round4ClosedParameterAtlas_smooth B hcover hB
  obtain ⟨hchi', hsupp', hpart', hD', hw', ht'⟩ := round4ClosedParameter_providers
    A B hcover chi hchi hchiSupport hpartition Bc T D hD hweight htransition
  have h := round4SpatialOuter_original_map_tail A B' R hR hA hB'
    rho hrho hbuffer m r htau htaul helt ht1 chi' hchi' hsupp' hpart' hu
    Bc T hBc hT D hD' hw' ht' hNr hNm budget hbudget
  dsimp only at h ⊢
  have heq := round4ClosedParameter_actual_map_eq A B hcover
    (volume : Measure (Ep × Es))
    (fixedSmoothingKernel (volume : Measure (Ep × Es)) rho hrho r) ell chi u
  change bufferedSmoothing (parameterProductAtlas A B') _ _ _ chi' _ = _ at heq
  rw [heq] at h
  exact h

theorem round4SpatialClosed_actual_map_gain
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i)
    (R : Fin A.count × Fin pcount → Set (Fin (n+d) → ℝ))
    (hR : ∀ i, R i ⊆ incrementsOriginalDifferentiation A B.chart i)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Ey} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) 0 (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) ≠ ⊤) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let C := parameterSpatialTransferCoefficient Es Ey Bc T
    let S := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
    let O := incrementsOriginalDifferentiation A B.chart
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ S ∧
    parameterSpatialWeighted (n := n) (d := d) m tau
      (incrementsOriginalMapCoordinates A B.chart S) O R ≠ ⊤ ∧
    (parameterSpatialWeighted (n := n) (d := d) m tau
      (incrementsOriginalMapCoordinates A B.chart S) O R).toReal ≤
      parameterModelSmoothingGainConstant cp cs cy mu K C T D m *
        (parameterSpatialCj (n := n) (d := d) 0
          (incrementsOriginalMapCoordinates A B.chart u) O (tensorLocalOriginalSampling A B)).toReal := by
  let B' := round4ClosedParameterAtlas B hcover
  let chi' := fun k => chi ((parameterTensorAtlasIndex A B').symm k)
  have hB' := round4ClosedParameterAtlas_smooth B hcover hB
  obtain ⟨hchi', hsupp', hpart', hD', hw', ht'⟩ := round4ClosedParameter_providers
    A B hcover chi hchi hchiSupport hpartition Bc T D hD hweight htransition
  have h := round4SpatialOuter_original_map_gain A B' R hR hA hB'
    rho hrho hbuffer m r hell hell1 htau htaul chi' hchi' hsupp' hu
    Bc T hBc hT D hD' hw' ht' hfinite
  dsimp only at h ⊢
  have heq := round4ClosedParameter_actual_map_eq A B hcover
    (volume : Measure (Ep × Es))
    (fixedSmoothingKernel (volume : Measure (Ep × Es)) rho hrho r) ell chi u
  change bufferedSmoothing (parameterProductAtlas A B') _ _ _ chi' _ = _ at heq
  rw [heq] at h
  exact h

end
end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4SpatialClosed_actual_map_tail
#print axioms GlobalEmbedding.Continuation.round4SpatialClosed_actual_map_gain
