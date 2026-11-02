import Smoothing.ParameterTotalNorms
import GlobalEmbedding.Offline.FixedSmoothingKernel
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-!
# Total-joint original base-two smoothing with nonzero parameters

This endpoint retains the literal frozen paperAtlasWeighted 2 map norm,
including pure parameter derivatives through j+2. It is distinct from the
spatial-two-jet packet endpoint. The actual global smoother, original source
and target models, coordinate ABI, sampling buffers and fixed kernel agree.
The parameter atlas B is finite and covers P; general local compact-K
preparation remains a separate obligation.
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

local instance parameterTotalSmoothingChartedSpace : ChartedSpace (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterTotalSmoothingIsManifold : IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
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

theorem fixedKernel_original_parameter_total_map_smoothing_tail
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
    (hNr : paperAtlasWeighted 2 r t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤)
    (hNm : paperAtlasWeighted 2 m t (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted 2 r t
      (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
      (parameterTensorOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let S := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
    let O := incrementsOriginalDifferentiation A B.chart
    let e := incrementsOriginalMapCoordinates A B.chart (fun z => u z - S z)
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ S ∧
    paperAtlasWeighted 2 m tau e O (parameterTensorOriginalInner A B) ≠ ⊤ ∧
    (paperAtlasWeighted 2 m tau e O (parameterTensorOriginalInner A B)).toReal ≤
      modelBufferedSmoothingTailConstant (parameterTensorModelEquiv n d) mu kappa Bc T D 2 m r *
        (budget * (ell / t) ^ r + (paperAtlasWeighted 2 m t
          (incrementsOriginalMapCoordinates A B.chart u) O
          (parameterTensorOriginalSampling A B)).toReal * (tau / t) ^ r) := by
  dsimp only
  let mu := (volume : Measure (Ep × Es))
  let K := fixedSmoothingKernel mu rho hrho r
  let S := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
  let c := parameterTensorModelEquiv n d
  have hAB := parameterProductAtlas_smooth A B hA hB
  haveI : mu.IsAddHaarMeasure := by
    dsimp only [mu]
    rw [Measure.volume_eq_prod]
    infer_instance
  have hb := normalizedSmoothingBase_spec mu rho hrho
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have huPi : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin q → ℝ) ∞ (cy ∘ u) :=
    (cy).contDiff.contMDiff.comp hu
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport hu
  have hSPi := parameterProductSmoothing_contMDiff A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer (htau.trans_le htaul).le (helt.trans ht1) chi hchi hchiSupport huPi
  have hNrLe := parameterTotalMap_weighted_sampling_le_original A B u 2 r t
  have hNmLe := parameterTotalMap_weighted_sampling_le_original A B u 2 m t
  have hNrN := ne_top_of_le_ne_top hNr hNrLe
  have hNmN := ne_top_of_le_ne_top hNm hNmLe
  have hbudgetN := (ENNReal.toReal_mono hNr hNrLe).trans hbudget
  have h := paperAtlasWeighted_model_buffered_smoothing_tail (parameterProductAtlas A B) c hAB mu
    hb.1 hb.2.1 hb.2.2.1 2 m r hK.2.2.1 hbuffer htau htaul helt ht1 chi hchi
    hchiSupport hpartition huPi Bc T hBc hT D hD hweight htransition hNrN hNmN budget hbudgetN
  dsimp only at h
  have hcomm := paperAtlasWeighted_model_buffered_sub_comm (parameterProductAtlas A B) hAB c 2 m tau
    (cy ∘ u) (bufferedSmoothing (parameterProductAtlas A B) mu K ell chi (cy ∘ u)) huPi hSPi
  dsimp only [K, fixedSmoothingKernel] at hcomm
  rw [← hcomm] at h
  have hnatural := bufferedSmoothing_equiv (parameterProductAtlas A B) mu K ell chi cy u
  have herror : bufferedModelCoordinates (parameterProductAtlas A B) c
      ((cy ∘ u) - bufferedSmoothing (parameterProductAtlas A B) mu K ell chi (cy ∘ u)) =
      bufferedModelCoordinates (parameterProductAtlas A B) c (cy ∘ (fun z => u z-S z)) := by
    rw [hnatural]
    funext i z
    exact ((cy).map_sub _ _).symm
  dsimp only [K, fixedSmoothingKernel] at herror
  rw [herror] at h
  have hEq := parameterTotalMap_weighted_inner_eq_original A B (fun z => u z-S z) 2 m tau
  rw [hEq] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  apply mul_le_mul_of_nonneg_left _
    (modelBufferedSmoothingTailConstant_nonneg c mu _ hBc hT D 2 m r)
  apply add_le_add le_rfl
  exact mul_le_mul_of_nonneg_right (ENNReal.toReal_mono hNm hNmLe)
    (pow_nonneg (div_nonneg htau.le ((htau.trans_le htaul).trans_le helt).le) _)

#print axioms fixedKernel_original_parameter_total_map_smoothing_tail
end
end GlobalEmbedding.Continuation
