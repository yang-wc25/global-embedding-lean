import Smoothing.Round4SpatialClosedMap
import Smoothing.Round4SpatialPairNorm
import Smoothing.Round3OuterOriginalMapGain
import Smoothing.Round3OuterOriginalTensorGain
import Smoothing.ParameterLocalOriginalPair
import Smoothing.ParameterLocalOriginalMapGain
import Smoothing.TensorLocalOriginalGain

/-!
# Actual closed-parameter pair with the literal spatial two-jet norm

The map uses only source derivatives of order at most two as its base.
All further derivatives are joint derivatives. The native tangent tensor
has its original base-zero norm. Both outputs are the existing actual
operators, with the same cutoff family, kernel and scale. No total-base-two
input norm is assumed or identified with the spatial-packet norm.
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

private local instance round4SpatialPairGainGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
private local instance round4SpatialPairGainGainIsManifold : IsManifold
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

theorem round4SpatialClosed_actual_pair_gain
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell : ℝ} (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : (Fin A.count × Fin pcount) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterLocalProductFamily A B).inner i)
    (hpartition : ∀ z : P × M, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Ey} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
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
    (hfinite : (parameterSpatialCj (n := n) (d := d) 0 (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)) ≠ ⊤)
    (budget : ℝ) (hbudget : (parameterSpatialCj (n := n) (d := d) 0 (incrementsOriginalMapCoordinates A B.chart u)
      (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B) +
      paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
        (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let Cmap := parameterModelSmoothingGainConstant cp cs cy mu K
      (parameterSpatialTransferCoefficient Es Ey Bc T) T D m
    let Ctensor := modelTensorSmoothingGainConstant n (parameterTensorModelEquiv n d)
      mu K Bc T (fun j => T (j+1)) D 0 m
    let Su := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
    let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ Su ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    round4ParameterSpatialPairWeighted A B Su SH m tau (incrementsOriginalDifferentiation A B.chart) ≠ ⊤ ∧
    (round4ParameterSpatialPairWeighted A B Su SH m tau (incrementsOriginalDifferentiation A B.chart)).toReal ≤
      max Cmap Ctensor * budget := by
  dsimp only
  let G := parameterSpatialCj (n := n) (d := d) 0 (incrementsOriginalMapCoordinates A B.chart u)
    (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)
  let Q := paperAtlasCj 0 (incrementsOriginalTensorCoordinates A B.chart H)
    (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)
  have hG : G ≠ ⊤ := (ENNReal.add_ne_top.mp hfinite).1
  have hQ : Q ≠ ⊤ := (ENNReal.add_ne_top.mp hfinite).2
  have hg := round4SpatialClosed_actual_map_gain A B hcover
    (incrementsOriginalDifferentiation A B.chart) (fun _ => Subset.rfl) hA hB rho hrho hbuffer m r
    hell hell1 htau htaul chi hchi hchiSupport hpartition hu Bc T hBc hT D hD hweight htransition hG
  have hq := round3Outer_fixedKernel_original_local_parameter_tensor_smoothing_gain A B hA hB rho hrho hbuffer m r
    htau hell htaul hell1 chi hchi hchiSupport H hH Bc T hBc hT D hD hweight htransition hQ
  dsimp only at hg hq
  let mu := (volume : Measure (Ep × Es))
  let K := fixedSmoothingKernel mu rho hrho r
  let Cg := parameterModelSmoothingGainConstant cp cs cy mu K
      (parameterSpatialTransferCoefficient Es Ey Bc T) T D m
  let Cq := modelTensorSmoothingGainConstant n (parameterTensorModelEquiv n d)
    mu K Bc T (fun j => T (j+1)) D 0 m
  have hCg : 0 ≤ Cg := parameterModelSmoothingGainConstant_nonneg cp cs cy
    mu K (parameterSpatialTransferCoefficient_nonneg Es Ey hBc hT) hT D m
  have hC : 0 ≤ max Cg Cq := hCg.trans (le_max_left _ _)
  have hbudget' : G.toReal+Q.toReal ≤ budget := by
    rw [← ENNReal.toReal_add hG hQ]
    exact hbudget
  refine ⟨hg.1,hq.1,ENNReal.add_ne_top.mpr ⟨hg.2.1,hq.2.1⟩,?_⟩
  rw [round4ParameterSpatialPairWeighted,ENNReal.toReal_add hg.2.1 hq.2.1]
  calc
    _ ≤ Cg*G.toReal+Cq*Q.toReal := add_le_add hg.2.2 hq.2.2
    _ ≤ max Cg Cq*G.toReal+max Cg Cq*Q.toReal :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _) ENNReal.toReal_nonneg)
        (mul_le_mul_of_nonneg_right (le_max_right _ _) ENNReal.toReal_nonneg)
    _ = max Cg Cq*(G.toReal+Q.toReal) := by ring
    _ ≤ max Cg Cq*budget := mul_le_mul_of_nonneg_left hbudget' hC

#print axioms round4SpatialClosed_actual_pair_gain
end
end GlobalEmbedding.Continuation
