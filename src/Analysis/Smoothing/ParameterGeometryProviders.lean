import Smoothing.ParameterGeometryCoefficient

/-!
# Original geometric providers produce the actual global transfer bounds

This closes the coefficient-provider boundary: C is the fixed model expression
parameterSpatialTransferCoefficient Es Y B T, chosen before any atlas, map, or
scale. Actual cutoff and transition derivatives through k+2 prove its k-th
operator bound. No derivative of the map being smoothed enters this step.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Ep Es P M Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [TopologicalSpace P] [TopologicalSpace M]
    [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
    [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

local instance parameterGeometryProvidersChartedSpace : ChartedSpace (Ep × Es) (P × M) :=
  prodChartedSpace Ep P Es M
local instance parameterGeometryProvidersIsManifold : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

variable (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
local notation "AB" => parameterProductAtlas A B
include hA hB

/-- The actual transferred source-two-jet coefficient has the prescribed bound
from only original full cutoff and transition jets through order k+2. -/
theorem parameterBufferedTransfer_jet_le
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (Bc T : ℕ → ℝ) (hBc : ∀ a, 0 ≤ Bc a) (hT : ∀ a, 0 ≤ T a)
    (p i : Fin (B.count * A.count)) {z : Ep × Es} (hz : z ∈ bufferedChartOverlap AB p i)
    (k : ℕ)
    (hweight : ∀ a ≤ k+2, ‖iteratedFDeriv ℝ a (chi i ∘ ((AB).chart p).symm) z‖ ≤ Bc a)
    (htransition : ∀ a, 1 ≤ a → a ≤ k+2 →
      ‖iteratedFDeriv ℝ a ((AB).chart i ∘ ((AB).chart p).symm) z‖ ≤ T a) :
    ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) z‖ ≤
      parameterSpatialTransferCoefficient Es Y Bc T k := by
  have hAB := parameterProductAtlas_smooth A B hA hB
  have hw : ContDiffOn ℝ ∞ (chi i ∘ ((AB).chart p).symm) (bufferedChartOverlap AB p i) := by
    letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
    exact ((hchi i).comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas (hAB.chart_mem p))).contDiffOn.mono
      (fun _ h => h.1)
  exact spatialTransferField_jet_le_of_geometry
    (B.chart (parameterProductIndex A B i).1 ∘ (B.chart (parameterProductIndex A B p).1).symm)
    (A.chart (parameterProductIndex A B i).2 ∘ (A.chart (parameterProductIndex A B p).2).symm)
    (bufferedChartOverlap_open AB p i) hw (bufferedTransition_contDiffOn AB hAB p i)
    Bc T hBc hT hz k hweight htransition

/-- Original uniform chart providers give the full uniform actual coefficient
provider used by global low/high/gain, with no independently assumed C field. -/
theorem parameterBufferedTransfer_bound_of_providers
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    (Bc T : ℕ → ℝ) (hBc : ∀ a, 0 ≤ Bc a) (hT : ∀ a, 0 ≤ T a)
    (hweight : ∀ p i a, ∀ z ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm z ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ a (chi i ∘ ((AB).chart p).symm) z‖ ≤ Bc a)
    (htransition : ∀ p i a, 1 ≤ a → ∀ z ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm z ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ a ((AB).chart i ∘ ((AB).chart p).symm) z‖ ≤ T a) :
    ∀ p i k, ∀ z ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm z ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) z‖ ≤
        parameterSpatialTransferCoefficient Es Y Bc T k := by
  intro p i k z hz hi
  exact parameterBufferedTransfer_jet_le A B hA hB chi hchi Bc T hBc hT p i
    ⟨hz.1,hchiSupport i hi⟩ k (fun a _ => hweight p i a z hz hi)
    (fun a ha _ => htransition p i a ha z hz hi)

#print axioms parameterBufferedTransfer_jet_le
#print axioms parameterBufferedTransfer_bound_of_providers
end
end GlobalEmbedding.Continuation
