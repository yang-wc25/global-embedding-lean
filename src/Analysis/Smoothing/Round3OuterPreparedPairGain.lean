import Smoothing.Round3OuterProviders
import Smoothing.Round3OuterOriginalPairGain
import Smoothing.ParameterLocalOriginalPairGain
import Smoothing.TensorLocalPrepared

/-!
# Uniform smoothing gain from actual source and parameter preparations

The constant is selected before either atlas, either raw bump family, either
field, all scales, and the budget. The raw preparations contain only actual
cutoffs, original support-graph degrees and original coordinate jet bounds.
The normalized product partition and every coefficient provider are produced.
The parameter chart family only needs the requested set preparation; it need
not cover P. Genuine C2/C0 sampling inputs give gain on all receiving chart
targets. The same normalized cutoff and fixed kernel as the local tail theorem
are used, with constants preceding pcount, atlases, Q and actual raw data.
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

local instance round3Outer_parameterLocalPreparedPairGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round3Outer_parameterLocalPreparedPairGainIsManifold : IsManifold
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

/-- A single uniform constant bounds the actual pair from its original total
C²-map plus C⁰-tensor input budget. The constant is chosen before the atlases,
raw cutoff families, the parameter set, fields, scales, and budget; the normalized product cutoff
and all transfer bounds are supplied by the actual preparations. -/
theorem round3Outer_exists_uniform_prepared_local_parameter_total_pair_smoothing_gain
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
      ∀ tau ell : ℝ, 0 < ell → ell ≤ 1 → 0 ≤ tau → tau ≤ ell →
      ∀ (u : P × M → Ey), (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Esource) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart u)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) +
       paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)) ≠ ⊤ →
      ∀ budget : ℝ,
      (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart u)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) +
       paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)).toReal ≤ budget →
      let mu := (volume : Measure (Eparameter × Esource))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff A B (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let Su := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Eparameter × Esource) 𝓘(ℝ, Ey) ∞ Su ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      parameterLocalOriginalTotalPairWeighted A B Su SH m tau (incrementsOriginalDifferentiation A B.chart) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B Su SH m tau (incrementsOriginalDifferentiation A B.chart)).toReal ≤
        C * budget := by
  obtain ⟨Bc, hBc, hprep⟩ := round3Outer_exists_uniform_local_product_smoothing_providers
    (Es := Esource) (Ep := Eparameter) (M := M) (P := P) BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp
  let T : ℕ → ℝ := fun j => max (TP j) (TS j)
  have hT : ∀ j, 0 ≤ T j := fun j => (hTP j).trans (le_max_left _ _)
  let D := (Ds+1)*(Dp+1)
  let mu := (volume : Measure (Eparameter × Esource))
  let K := fixedSmoothingKernel mu rho hrho r
  let Cg := modelBufferedSmoothingGainConstant (parameterTensorModelEquiv n d) mu K Bc T D 2 m
  let Cq := modelTensorSmoothingGainConstant n (parameterTensorModelEquiv n d)
    mu K Bc T (fun j => T (j+1)) D 0 m
  refine ⟨max Cg Cq, ?_, ?_⟩
  · exact (modelBufferedSmoothingGainConstant_nonneg (parameterTensorModelEquiv n d) mu K hBc hT D 2 m).trans (le_max_left _ _)
  intro pcount A B hA hB Q RS RP hbuffer tau ell hell hell1 htau htaul u hu H hH hfinite budget hbudget
  obtain ⟨W, hW, hQW, hchi, _hpartition, hsupport, hD, hweight, htransition⟩ := hprep pcount A B hA hB Q RS RP
  exact round3Outer_fixedKernel_original_local_parameter_total_pair_smoothing_gain A B hA hB rho hrho hbuffer m r
    hell hell1 htau htaul _ hchi hsupport hu H hH Bc T hBc hT D hD hweight htransition
    hfinite budget hbudget

#print axioms round3Outer_exists_uniform_prepared_local_parameter_total_pair_smoothing_gain
end
end GlobalEmbedding.Continuation
