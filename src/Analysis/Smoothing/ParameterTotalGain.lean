import Smoothing.ParameterTotalSmoothing

/-!
# Gain in the literal frozen total-joint base-two original map norm

The unchanged Core map norm includes all joint derivatives through j+2.
The same global native map smoother gains weighted joint derivatives from
its true original total C2 input, using the same fixed kernel of order r.
This is not an inference from the distinct anisotropic spatial packet.
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

local instance parameterTotalGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterTotalGainIsManifold : IsManifold
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

theorem fixedKernel_original_parameter_total_map_smoothing_gain
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
    (hfinite : paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B) ≠ ⊤) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let S := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
    let O := incrementsOriginalDifferentiation A B.chart
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ S ∧
    paperAtlasWeighted 2 m tau
      (incrementsOriginalMapCoordinates A B.chart S) O (parameterTensorOriginalInner A B) ≠ ⊤ ∧
    (paperAtlasWeighted 2 m tau
      (incrementsOriginalMapCoordinates A B.chart S) O (parameterTensorOriginalInner A B)).toReal ≤
      modelBufferedSmoothingGainConstant (parameterTensorModelEquiv n d) mu K Bc T D 2 m *
        (paperAtlasCj 2
          (incrementsOriginalMapCoordinates A B.chart u) O (parameterTensorOriginalSampling A B)).toReal := by
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
  have hK := fixedSmoothingKernel_spec mu rho hrho r
  have huPi : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Fin q → ℝ) ∞ (cy ∘ u) :=
    (cy).contDiff.contMDiff.comp hu
  have hNLe := parameterTotalMap_Cj_sampling_le_original A B u 2
  have hNN := ne_top_of_le_ne_top hfinite hNLe
  have h := paperAtlasWeighted_model_buffered_smoothing_gain (parameterProductAtlas A B) c hAB mu
    hK.1 hK.2.1 hK.2.2.1 hbuffer hell hell1 htau htaul chi hchi
    hchiSupport huPi Bc T hBc hT D hD hweight htransition 2 m hNN
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu hK.1 hK.2.1 hK.2.2.1
    hbuffer hell.le hell1 chi hchi hchiSupport hu
  dsimp only at h
  rw [bufferedSmoothing_equiv] at h
  have hEq := parameterTotalMap_weighted_inner_eq_original A B S 2 m tau
  rw [hEq] at h
  refine ⟨hS, h.1, h.2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left (ENNReal.toReal_mono hfinite hNLe)
    (modelBufferedSmoothingGainConstant_nonneg c mu K hBc hT D 2 m)

#print axioms fixedKernel_original_parameter_total_map_smoothing_gain
end
end GlobalEmbedding.Continuation
