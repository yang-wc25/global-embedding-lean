import Smoothing.ParameterOriginalABI
import Smoothing.ParameterGeometryProviders
import Smoothing.IntegrationParameterWeighted
import GlobalEmbedding.Offline.FixedSmoothingKernel
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Fixed-kernel global map smoothing in the literal original parameter ABI

The source-first original coordinates, spatial two-jet followed by joint
derivatives, original product sampling buffers, and chart maximum are retained.
All actual coefficient bounds are produced from cutoff and transition jets.
The constant is fixed by n,d,q,rho,Bc,T,D,m,r before the atlas, map, and scales.

This spatial-packet norm is not the frozen CoreInputProfile's total-joint
paperAtlasWeighted 2 norm for nonzero parameter dimension. The exact stronger
frozen endpoint is ParameterTotalSmoothing; no equality of these norms is claimed.

The parameter atlas B is finite and covers all P. This theorem does not assert
that arbitrary local chart data near a compact K produces such a global atlas.
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

local instance parameterOriginalSmoothingChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterOriginalSmoothingIsManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
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

/-- The actual spatial-packet analogue of the global map half of (6.4), with one fixed signed moment kernel,
literal original map coordinates, original independent sampling buffers,
and no independent transfer-coefficient assumption. -/
theorem fixedKernel_original_parameter_map_smoothing_tail
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Ey} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ T k)
    (hNr : parameterSpatialWeighted (n := n) (d := d) r t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤)
    (hNm : parameterSpatialWeighted (n := n) (d := d) m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget : (parameterSpatialWeighted (n := n) (d := d) r t
      (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
      (parameterTensorOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let C := parameterSpatialTransferCoefficient Es Ey Bc T
    let S := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
    let O := incrementsOriginalDifferentiation A B.chart
    let e := incrementsOriginalMapCoordinates A B.chart (fun z => u z - S z)
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ S ∧
    parameterSpatialWeighted (n := n) (d := d) m tau e O (parameterTensorOriginalInner A B) ≠ ⊤ ∧
    (parameterSpatialWeighted (n := n) (d := d) m tau e O (parameterTensorOriginalInner A B)).toReal ≤
      parameterModelSmoothingTailConstant cp cs cy mu kappa C T D m r *
        (budget * (ell / t) ^ r + (parameterSpatialWeighted (n := n) (d := d) m t
          (incrementsOriginalMapCoordinates A B.chart u) O
          (parameterTensorOriginalSampling A B)).toReal * (tau / t) ^ r) := by
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
  have hb := normalizedSmoothingBase_spec mu rho hrho
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have hNrLe := parameterMap_weighted_sampling_le_original A B u r t
  have hNmLe := parameterMap_weighted_sampling_le_original A B u m t
  have hNrN := ne_top_of_le_ne_top hNr hNrLe
  have hNmN := ne_top_of_le_ne_top hNm hNmLe
  have hbudgetN := (ENNReal.toReal_mono hNr hNrLe).trans hbudget
  have hc := parameterBufferedTransfer_bound_of_providers (Y := Ey) A B hA hB chi hchi
    hchiSupport Bc T hBc hT hweight htransition
  have h := parameterBufferedSmoothing_original_weighted_tail A B hA hB cp cs cy mu
    hb.1 hb.2.1 hb.2.2.1 m r hK.2.2.1 hbuffer htau htaul helt ht1 chi hchi
    hchiSupport hpartition hu C T hC hT D hD hc htransition hNrN hNmN budget hbudgetN
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport hu
  have hEq := parameterMap_weighted_inner_eq_original A B (fun z => S z - u z) m tau
  dsimp only at h
  dsimp only [S, K, fixedSmoothingKernel] at hEq
  rw [hEq] at h
  have hcomm := parameterOriginalMap_weighted_sub_comm A B hA hB u S hu hS m tau
    (parameterTensorOriginalInner A B) (parameterTensorOriginalInner_subset A B)
  dsimp only [S, K, fixedSmoothingKernel] at hcomm
  rw [← hcomm] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _
    (parameterModelSmoothingTailConstant_nonneg cp cs cy mu _ hC hT D m r)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hNm hNmLe)
    (pow_nonneg (div_nonneg htau.le ((htau.trans_le htaul).trans_le helt).le) _)

#print axioms fixedKernel_original_parameter_map_smoothing_tail
end
end GlobalEmbedding.Continuation
