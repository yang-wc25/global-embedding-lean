import Smoothing.Round3OuterOriginalMapGain
import Smoothing.Round3OuterOriginalTensorGain
import Smoothing.ParameterLocalOriginalPair
import Smoothing.ParameterLocalOriginalMapGain
import Smoothing.TensorLocalOriginalGain

/-!
# One actual pair gains every weighted slow norm from original C2 and C0

The map uses the literal frozen total-joint base-two norm, the tensor uses
base zero, and both actual smoothers use the same fixed kernel and scale.
Only the original C2-map/C0-tensor input budget occurs on the right.
The parameter family need not cover P. The SAME actual pair and the original
full joint norms from the local tail theorem are used. The output estimate
holds on full receiving chart targets; only actual sampling-buffer inputs are used.
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

local instance round3Outer_parameterLocalOriginalPairGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance round3Outer_parameterLocalOriginalPairGainIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin q)
local notation "cp" => EuclideanSpace.equiv (Fin d) ℝ
local notation "cs" => EuclideanSpace.equiv (Fin n) ℝ
local notation "cy" => EuclideanSpace.equiv (Fin q) ℝ

theorem round3Outer_fixedKernel_original_local_parameter_total_pair_smoothing_gain
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    {u : P × M → Ey} (hu : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalMapCoordinates A B.chart u i)
      (incrementsOriginalDifferentiation A B.chart i))
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i))
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((parameterLocalProductFamily A B).chart p).target,
      ((parameterLocalProductFamily A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterLocalProductFamily A B).chart i ∘ ((parameterLocalProductFamily A B).chart p).symm) y‖ ≤ T k)
    (hfinite : (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let Cmap := modelBufferedSmoothingGainConstant (parameterTensorModelEquiv n d) mu K Bc T D 2 m
    let Ctensor := modelTensorSmoothingGainConstant n (parameterTensorModelEquiv n d)
      mu K Bc T (fun j => T (j+1)) D 0 m
    let Su := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
    let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ Su ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    parameterLocalOriginalTotalPairWeighted A B Su SH m tau (incrementsOriginalDifferentiation A B.chart) ≠ ⊤ ∧
    (parameterLocalOriginalTotalPairWeighted A B Su SH m tau (incrementsOriginalDifferentiation A B.chart)).toReal ≤
      max Cmap Ctensor * budget := by
  dsimp only
  let G := paperAtlasCj 2 (incrementsOriginalMapCoordinates A B.chart u)
    (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)
  let Q := paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
    (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)
  have hG : G ≠ ⊤ := (ENNReal.add_ne_top.mp hfinite).1
  have hQ : Q ≠ ⊤ := (ENNReal.add_ne_top.mp hfinite).2
  have hg := round3Outer_fixedKernel_original_local_parameter_total_map_smoothing_gain A B hA hB rho hrho hbuffer m r
    hell hell1 htau htaul chi hchi hchiSupport hu Bc T hBc hT D hD hweight htransition hG
  have hq := round3Outer_fixedKernel_original_local_parameter_tensor_smoothing_gain A B hA hB rho hrho hbuffer m r
    htau hell htaul hell1 chi hchi hchiSupport H hH Bc T hBc hT D hD hweight htransition hQ
  dsimp only at hg hq
  let mu := (volume : Measure (Ep × Es))
  let K := fixedSmoothingKernel mu rho hrho r
  let Cg := modelBufferedSmoothingGainConstant (parameterTensorModelEquiv n d) mu K Bc T D 2 m
  let Cq := modelTensorSmoothingGainConstant n (parameterTensorModelEquiv n d)
    mu K Bc T (fun j => T (j+1)) D 0 m
  have hCg : 0 ≤ Cg := modelBufferedSmoothingGainConstant_nonneg (parameterTensorModelEquiv n d)
    mu K hBc hT D 2 m
  have hC : 0 ≤ max Cg Cq := hCg.trans (le_max_left _ _)
  have hbudget' : G.toReal+Q.toReal ≤ budget := by
    rw [← ENNReal.toReal_add hG hQ]
    exact hbudget
  refine ⟨hg.1,hq.1,ENNReal.add_ne_top.mpr ⟨hg.2.1,hq.2.1⟩,?_⟩
  rw [parameterLocalOriginalTotalPairWeighted,ENNReal.toReal_add hg.2.1 hq.2.1]
  calc
    _ ≤ Cg*G.toReal+Cq*Q.toReal := add_le_add hg.2.2 hq.2.2
    _ ≤ max Cg Cq*G.toReal+max Cg Cq*Q.toReal :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)
    _ = max Cg Cq*(G.toReal+Q.toReal) := by ring
    _ ≤ max Cg Cq*budget := mul_le_mul_of_nonneg_left hbudget' hC

#print axioms round3Outer_fixedKernel_original_local_parameter_total_pair_smoothing_gain
end
end GlobalEmbedding.Continuation
