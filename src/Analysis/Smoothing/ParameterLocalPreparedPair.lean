import Smoothing.ParameterLocalOriginalPair
import Smoothing.TensorLocalPrepared

/-!
# Uniform original pair (6.4) from raw preparations near only the parameter set

The constant is chosen before either atlas/family, the compact parameter set,
raw bumps, fields, scales, and budget. The parameter family need not cover P.
Actual raw local preparations produce the normalized product cutoff, every
cutoff/transition provider, and an open W containing the requested set Q.
The same signed kernel and scale smooth the Euclidean map and source tensor.
The map norm remains literal total joint base two, and the tensor base zero.

Input norms are required on the genuine fixed independent sampling buffers
(with parameterSet=univ). No inference enlarges a budget restricted to Q.
Thus the remaining repair-data-to-sampling-domain obligation is explicit.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {n d q pcount : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance parameterLocalPreparedPairChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterLocalPreparedPairIsManifold : IsManifold
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
in the preparation inputs. The support-degree factor is (Ds+1)*(Dp+1). -/
theorem exists_uniform_prepared_local_parameter_total_pair_smoothing_tail
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧
      ∀ (pcount : ℕ) (A : BufferedAtlas M Esource) (B : TensorBufferedChartFamily (Fin pcount) P Eparameter)
        (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Eparameter) ∞ P)
        (Q : Set P) (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B Q BP₀ TP Dp),
      rho ≤ min B.buffer A.buffer →
      ∃ W : Set P, IsOpen W ∧ Q ⊆ W ∧
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Esource) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      parameterLocalOriginalTotalPairWeighted A B u H r t (tensorLocalOriginalSampling A B) ≠ ⊤ →
      parameterLocalOriginalTotalPairWeighted A B u H m t (tensorLocalOriginalSampling A B) ≠ ⊤ →
      ∀ budget : ℝ,
      (parameterLocalOriginalTotalPairWeighted A B u H r t (tensorLocalOriginalSampling A B)).toReal ≤ budget →
      let mu := (volume : Measure (Eparameter × Esource))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let Su := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ Su ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
        m tau (tensorLocalOriginalInner A B W) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
        m tau (tensorLocalOriginalInner A B W)).toReal ≤
        C * (budget*(ell/t)^r +
          (parameterLocalOriginalTotalPairWeighted A B u H m t (tensorLocalOriginalSampling A B)).toReal*(tau/t)^r) := by
  obtain ⟨Bc, hBc, hprep⟩ := exists_uniform_local_product_smoothing_providers
    (Es := Esource) (Ep := Eparameter) (M := M) (P := P) BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp
  let T : ℕ → ℝ := fun j => max (TP j) (TS j)
  have hT : ∀ j, 0 ≤ T j := fun j => (hTP j).trans (le_max_left _ _)
  let D := (Ds+1)*(Dp+1)
  let mu := (volume : Measure (Eparameter × Esource))
  let kappa := normalizedSmoothingBase mu rho hrho
  let Cg := modelBufferedSmoothingTailConstant (parameterTensorModelEquiv n d) mu kappa Bc T D 2 m r
  let Cq := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d)
    mu kappa Bc T (fun j => T (j+1)) D 0 m r
  refine ⟨max Cg Cq, ?_, ?_⟩
  · exact (modelBufferedSmoothingTailConstant_nonneg (parameterTensorModelEquiv n d) mu kappa hBc hT D 2 m r).trans (le_max_left _ _)
  intro pcount A B hA hB Q RS RP hbuffer
  obtain ⟨W,hW,hQW,hchi,hpartition,hsupport,hD,hweight,htransition⟩ := hprep pcount A B hA hB Q RS RP
  refine ⟨W,hW,hQW,?_⟩
  intro tau ell t htau htaul helt ht1 u hu H hH hNr hNm budget hbudget
  exact fixedKernel_original_local_parameter_total_pair_smoothing_tail A B hA hB rho hrho hbuffer m r
    htau htaul helt ht1 _ hchi hsupport W hW hpartition hu H hH Bc T hBc hT D hD hweight htransition
    hNr hNm budget hbudget

#print axioms exists_uniform_prepared_local_parameter_total_pair_smoothing_tail
end
end GlobalEmbedding.Continuation
