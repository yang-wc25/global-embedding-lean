import Smoothing.Round4TensorFiniteProviders
import Smoothing.Round3OuterOriginalPair
import Smoothing.Round3OuterOriginalPairGain

/-!
# Original map/tensor (6.4) with finite raw-geometry constants

The selected constants are literal finite expressions in the original raw
cutoff and coordinate-transition bounds. Changing any raw entry after m+2
leaves both constants exactly equal. The same original signed kernel, actual
normalized cutoffs, actual map and source-tangent tensor are retained.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

def round4PreparedPairTailConstant (n d : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (BS₀ TS BP₀ TP : ℕ → ℝ) (Ds Dp m r : ℕ) : ℝ :=
  let c := parameterTensorModelEquiv n d
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let kappa := normalizedSmoothingBase mu rho hrho
  let Bc := round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp
  let T := fun j => max (TP j) (TS j)
  let D := (Ds+1)*(Dp+1)
  max (modelBufferedSmoothingTailConstant c mu kappa Bc T D 2 m r)
    (modelTensorSmoothingTailConstant n c mu kappa Bc T (fun j => T (j+1)) D 0 m r)

def round4PreparedPairGainConstant (n d : ℕ) (rho : ℝ) (hrho : 0 < rho)
    (BS₀ TS BP₀ TP : ℕ → ℝ) (Ds Dp m r : ℕ) : ℝ :=
  let c := parameterTensorModelEquiv n d
  let mu := (volume : Measure (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)))
  let K := fixedSmoothingKernel mu rho hrho r
  let Bc := round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp
  let T := fun j => max (TP j) (TS j)
  let D := (Ds+1)*(Dp+1)
  max (modelBufferedSmoothingGainConstant c mu K Bc T D 2 m)
    (modelTensorSmoothingGainConstant n c mu K Bc T (fun j => T (j+1)) D 0 m)

/-- No hidden choice of an infinite normalized profile occurs in this equality. -/
theorem round4PreparedPairTailConstant_congr_prefix
    (n d : ℕ) (rho : ℝ) (hrho : 0 < rho) (Ds Dp m r : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ m+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ m+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ m+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ m+2, TP₁ a = TP₂ a) :
    round4PreparedPairTailConstant n d rho hrho BS₁ TS₁ BP₁ TP₁ Ds Dp m r =
      round4PreparedPairTailConstant n d rho hrho BS₂ TS₂ BP₂ TP₂ Ds Dp m r := by
  apply parameterTotalPairTailConstant_congr_prefix
  · intro a ha
    exact round4ProductCutoffProfile_congr_prefix Ds Dp a
      (fun k hk => hBS k (hk.trans ha)) (fun k hk => hTS k (hk.trans ha))
      (fun k hk => hBP k (hk.trans ha)) (fun k hk => hTP k (hk.trans ha))
  · intro a ha
    rw [hTP a ha,hTS a ha]

theorem round4TensorGainConstant_congr_prefix
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {k : ℕ}
    (n : ℕ) (c : E ≃L[ℝ] (Fin k → ℝ)) (mu : Measure E) (K : E → ℝ)
    {B₁ B₂ T₁ T₂ : ℕ → ℝ} (D m : ℕ)
    (hB : ∀ a ≤ m, B₁ a = B₂ a) (hT : ∀ a ≤ m+1, T₁ a = T₂ a) :
    modelTensorSmoothingGainConstant n c mu K B₁ T₁ (fun j => T₁ (j+1)) D 0 m =
      modelTensorSmoothingGainConstant n c mu K B₂ T₂ (fun j => T₂ (j+1)) D 0 m := by
  unfold modelTensorSmoothingGainConstant
  apply Finset.sum_congr rfl
  intro j hj
  have hjm : j ≤ m := by simpa using hj
  unfold modelTensorTransferConstant
  simp only [Nat.add_zero]
  rw [parameterTensorTransferConstant_congr_prefix n D j
    (fun a ha => hB a (ha.trans hjm))
    (fun a ha => hT a (by omega)) (fun a ha => hT (a+1) (by omega))]

/-- The same m+2 raw prefix controls the gain of the very same smoother. -/
theorem round4PreparedPairGainConstant_congr_prefix
    (n d : ℕ) (rho : ℝ) (hrho : 0 < rho) (Ds Dp m r : ℕ)
    {BS₁ BS₂ TS₁ TS₂ BP₁ BP₂ TP₁ TP₂ : ℕ → ℝ}
    (hBS : ∀ a ≤ m+2, BS₁ a = BS₂ a) (hTS : ∀ a ≤ m+2, TS₁ a = TS₂ a)
    (hBP : ∀ a ≤ m+2, BP₁ a = BP₂ a) (hTP : ∀ a ≤ m+2, TP₁ a = TP₂ a) :
    round4PreparedPairGainConstant n d rho hrho BS₁ TS₁ BP₁ TP₁ Ds Dp m r =
      round4PreparedPairGainConstant n d rho hrho BS₂ TS₂ BP₂ TP₂ Ds Dp m r := by
  have hBc (a : ℕ) (ha : a ≤ m+2) := round4ProductCutoffProfile_congr_prefix Ds Dp a
    (fun k hk => hBS k (hk.trans ha)) (fun k hk => hTS k (hk.trans ha))
    (fun k hk => hBP k (hk.trans ha)) (fun k hk => hTP k (hk.trans ha))
  have hT (a : ℕ) (ha : a ≤ m+2) : max (TP₁ a) (TS₁ a) = max (TP₂ a) (TS₂ a) := by
    rw [hTP a ha,hTS a ha]
  unfold round4PreparedPairGainConstant
  dsimp only
  rw [parameterTotalMapGainConstant_congr_prefix _ _ _ _ m hBc hT,
    round4TensorGainConstant_congr_prefix n _ _ _ _ m
      (fun a ha => hBc a (by omega)) (fun a ha => hT a (by omega))]

variable {n d q : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

local instance : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Eparameter" => EuclideanSpace ℝ (Fin d)
local notation "Esource" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)


/-- The original tail estimate with a selected finite raw-geometry constant. -/
theorem round4_prepared_original_pair_tail
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    let C := round4PreparedPairTailConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r
    0 ≤ C ∧
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
        m tau (round3OuterOriginalEvaluation A B W) ≠ ⊤ ∧
      (parameterLocalOriginalTotalPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
        m tau (round3OuterOriginalEvaluation A B W)).toReal ≤
        C * (budget*(ell/t)^r +
          (parameterLocalOriginalTotalPairWeighted A B u H m t (tensorLocalOriginalSampling A B)).toReal*(tau/t)^r) := by
  let Bc := round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp
  have hBc : ∀ j, 0 ≤ Bc j := round4ProductCutoffProfile_nonneg hBS₀ hTS hBP₀ hTP Ds Dp
  let T : ℕ → ℝ := fun j => max (TP j) (TS j)
  have hT : ∀ j, 0 ≤ T j := fun j => (hTP j).trans (le_max_left _ _)
  let D := (Ds+1)*(Dp+1)
  let mu := (volume : Measure (Eparameter × Esource))
  let kappa := normalizedSmoothingBase mu rho hrho
  let Cg := modelBufferedSmoothingTailConstant (parameterTensorModelEquiv n d) mu kappa Bc T D 2 m r
  let Cq := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d)
    mu kappa Bc T (fun j => T (j+1)) D 0 m r
  refine ⟨?_, ?_⟩
  · exact (modelBufferedSmoothingTailConstant_nonneg (parameterTensorModelEquiv n d) mu kappa hBc hT D 2 m r).trans (le_max_left _ _)
  intro pcount A B hA hB Q RS RP hbuffer
  obtain ⟨W,hW,hQW,hchi,hpartition,hsupport,hD,hweight,htransition⟩ := round4_actual_product_smoothing_providers BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp pcount A B hA hB Q RS RP
  refine ⟨W,hW,hQW,?_⟩
  intro tau ell t htau htaul helt ht1 u hu H hH hNr hNm budget hbudget
  exact round3Outer_fixedKernel_original_local_parameter_total_pair_smoothing_tail A B hA hB rho hrho hbuffer m r
    htau htaul helt ht1 _ hchi hsupport W hW hpartition hu H hH Bc T hBc hT D hD hweight htransition
    hNr hNm budget hbudget


/-- The original gain estimate with a selected finite raw-geometry constant. -/
theorem round4_prepared_original_pair_gain
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    let C := round4PreparedPairGainConstant n d rho hrho BS₀ TS BP₀ TP Ds Dp m r
    0 ≤ C ∧
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
  let Bc := round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp
  have hBc : ∀ j, 0 ≤ Bc j := round4ProductCutoffProfile_nonneg hBS₀ hTS hBP₀ hTP Ds Dp
  let T : ℕ → ℝ := fun j => max (TP j) (TS j)
  have hT : ∀ j, 0 ≤ T j := fun j => (hTP j).trans (le_max_left _ _)
  let D := (Ds+1)*(Dp+1)
  let mu := (volume : Measure (Eparameter × Esource))
  let K := fixedSmoothingKernel mu rho hrho r
  let Cg := modelBufferedSmoothingGainConstant (parameterTensorModelEquiv n d) mu K Bc T D 2 m
  let Cq := modelTensorSmoothingGainConstant n (parameterTensorModelEquiv n d)
    mu K Bc T (fun j => T (j+1)) D 0 m
  refine ⟨?_, ?_⟩
  · exact (modelBufferedSmoothingGainConstant_nonneg (parameterTensorModelEquiv n d) mu K hBc hT D 2 m).trans (le_max_left _ _)
  intro pcount A B hA hB Q RS RP hbuffer tau ell hell hell1 htau htaul u hu H hH hfinite budget hbudget
  obtain ⟨W, hW, hQW, hchi, _hpartition, hsupport, hD, hweight, htransition⟩ := round4_actual_product_smoothing_providers BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP Ds Dp pcount A B hA hB Q RS RP
  exact round3Outer_fixedKernel_original_local_parameter_total_pair_smoothing_gain A B hA hB rho hrho hbuffer m r
    hell hell1 htau htaul _ hchi hsupport hu H hH Bc T hBc hT D hD hweight htransition
    hfinite budget hbudget


#print axioms round4PreparedPairTailConstant_congr_prefix
#print axioms round4PreparedPairGainConstant_congr_prefix
#print axioms round4_prepared_original_pair_tail
#print axioms round4_prepared_original_pair_gain
end
end GlobalEmbedding.Continuation
