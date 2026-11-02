import Smoothing.ParameterTotalPairSmoothing
import Smoothing.TensorPreparedProduct

/-!
# A uniform frozen-total-joint pair endpoint from the actual source and parameter preparations

The constant is selected before either atlas, either raw bump family, either
field, all scales, and the budget. The raw preparations contain only actual
cutoffs, original support-graph degrees and original coordinate jet bounds.
The normalized product partition and every coefficient provider are produced.
This still requires finite atlases covering M and P; no compact-subset cover
is silently replaced by a global parameter atlas.
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

local instance parameterPreparedTotalPairChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterPreparedTotalPairIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Eparameter" => EuclideanSpace ℝ (Fin d)
local notation "Esource" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)
local notation "cp" => EuclideanSpace.equiv (Fin d) ℝ
local notation "cs" => EuclideanSpace.equiv (Fin n) ℝ
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ

/-- The original pair estimate with its constant quantified before all finite
atlases and actual preparations. No output estimate or transfer jet is stored
in the preparation inputs. The support-degree factor is (Dp+1)*(Ds+1). -/
theorem exists_uniform_prepared_parameter_total_pair_smoothing_tail
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (A : BufferedAtlas M Esource) (B : BufferedAtlas P Eparameter)
        (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
        (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorRawCutoffPreparation B BP₀ TP Dp),
      rho ≤ min B.buffer A.buffer →
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey), ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ u →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Esource) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      parameterOriginalTotalPairWeighted A B u H r t (parameterTensorOriginalSampling A B) ≠ ⊤ →
      parameterOriginalTotalPairWeighted A B u H m t (parameterTensorOriginalSampling A B) ≠ ⊤ →
      ∀ budget : ℝ,
      (parameterOriginalTotalPairWeighted A B u H r t (parameterTensorOriginalSampling A B)).toReal ≤ budget →
      let mu := (volume : Measure (Eparameter × Esource))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := tensorProductCutoff A B (squareNormalizedCutoff RS.raw) (squareNormalizedCutoff RP.raw)
      let Su := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
      let SH := parameterNativeTensorSmoothing A B hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ Su ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterOriginalTotalPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
        m tau (parameterTensorOriginalInner A B) ≠ ⊤ ∧
      (parameterOriginalTotalPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
        m tau (parameterTensorOriginalInner A B)).toReal ≤
        C * (budget*(ell/t)^r +
          (parameterOriginalTotalPairWeighted A B u H m t (parameterTensorOriginalSampling A B)).toReal*(tau/t)^r) := by
  obtain ⟨Bc, hBc, hprep⟩ := exists_uniform_prepared_product_smoothing_providers
    (Es := Esource) (Ep := Eparameter) (M := M) (P := P) BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp
  let T : ℕ → ℝ := fun j => max (TP j) (TS j)
  have hT : ∀ j, 0 ≤ T j := fun j => (hTP j).trans (le_max_left _ _)
  let D := (Dp+1)*(Ds+1)
  let mu := (volume : Measure (Eparameter × Esource))
  let kappa := normalizedSmoothingBase mu rho hrho
  let Cg := modelBufferedSmoothingTailConstant (parameterTensorModelEquiv n d) mu kappa Bc T D 2 m r
  let Cq := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d)
    mu kappa Bc T (fun j => T (j+1)) D 0 m r
  refine ⟨max Cg Cq, ?_, ?_⟩
  · exact (modelBufferedSmoothingTailConstant_nonneg (parameterTensorModelEquiv n d) mu kappa hBc hT D 2 m r).trans (le_max_left _ _)
  intro A B hA hB RS RP hbuffer tau ell t htau htaul helt ht1 u hu H hH hNr hNm budget hbudget
  obtain ⟨hchi, hpartition, hsupport, hD, hweight, htransition⟩ := hprep A B hA hB RS RP
  exact fixedKernel_original_parameter_total_pair_smoothing_tail A B hA hB rho hrho hbuffer m r
    htau htaul helt ht1 _ hchi hsupport hpartition hu H hH Bc T hBc hT D hD hweight htransition
    hNr hNm budget hbudget

#print axioms exists_uniform_prepared_parameter_total_pair_smoothing_tail
end
end GlobalEmbedding.Continuation
