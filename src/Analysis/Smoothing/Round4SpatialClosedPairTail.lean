import Smoothing.Round4SpatialClosedMap
import Smoothing.Round4SpatialPairNorm
import Smoothing.Round3OuterOriginalMap
import Smoothing.Round3OuterOriginalTensor
import Smoothing.ParameterLocalOriginalMap
import Smoothing.TensorLocalOriginal

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

private local instance round4SpatialPairTailChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
private local instance round4SpatialPairTailIsManifold : IsManifold
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

/-- Equation (6.4) for the actual pair, with a single original input budget
and a single uniform constant, including finiteness before conversion to R. -/
theorem round4SpatialClosed_actual_pair_tail
    (A : BufferedAtlas M Es) (B : TensorBufferedChartFamily (Fin pcount) P Ep)
    (hcover : ∀ p, ∃ i, p ∈ B.inner i)
    (hA : IsSmoothBufferedAtlas A) (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
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
    (hNr : round4ParameterSpatialPairWeighted A B u H r t (tensorLocalOriginalSampling A B) ≠ ⊤)
    (hNm : round4ParameterSpatialPairWeighted A B u H m t (tensorLocalOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget :
      (round4ParameterSpatialPairWeighted A B u H r t (tensorLocalOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let Cmap := parameterModelSmoothingTailConstant cp cs cy mu kappa
      (parameterSpatialTransferCoefficient Es Ey Bc T) T D m r
    let Ctensor := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d)
      mu kappa Bc T (fun j => T (j+1)) D 0 m r
    let Su := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
    let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ Su ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    round4ParameterSpatialPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
      m tau (incrementsOriginalDifferentiation A B.chart) ≠ ⊤ ∧
    (round4ParameterSpatialPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
      m tau (incrementsOriginalDifferentiation A B.chart)).toReal ≤
      max Cmap Ctensor * (budget * (ell/t)^r +
        (round4ParameterSpatialPairWeighted A B u H m t (tensorLocalOriginalSampling A B)).toReal * (tau/t)^r) := by
  dsimp only
  let G (j : ℕ) := parameterSpatialWeighted (n := n) (d := d) j t
    (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
    (tensorLocalOriginalSampling A B)
  let Q (j : ℕ) := paperAtlasWeighted 0 j t (incrementsOriginalTensorCoordinates A B.chart H)
    (incrementsOriginalDifferentiation A B.chart) (tensorLocalOriginalSampling A B)
  have hGr : G r ≠ ⊤ := (ENNReal.add_ne_top.mp hNr).1
  have hQr : Q r ≠ ⊤ := (ENNReal.add_ne_top.mp hNr).2
  have hGm : G m ≠ ⊤ := (ENNReal.add_ne_top.mp hNm).1
  have hQm : Q m ≠ ⊤ := (ENNReal.add_ne_top.mp hNm).2
  have hg := round4SpatialClosed_actual_map_tail A B hcover
    (incrementsOriginalDifferentiation A B.chart) (fun _ => Subset.rfl) hA hB rho hrho hbuffer m r
    htau htaul helt ht1 chi hchi hchiSupport hpartition hu Bc T hBc hT D hD hweight htransition
    hGr hGm (G r).toReal le_rfl
  have hq := round3Outer_fixedKernel_original_local_parameter_tensor_smoothing_tail A B hA hB rho hrho hbuffer m r
    htau htaul helt ht1 chi hchi hchiSupport univ isOpen_univ (fun z _ => hpartition z) H hH Bc T hBc hT D hD hweight htransition
    hQr hQm (Q r).toReal le_rfl
  dsimp only at hg hq
  rw [round3OuterOriginalEvaluation_univ] at hq
  let mu := (volume : Measure (Ep × Es))
  let kappa := normalizedSmoothingBase mu rho hrho
  let Cg := parameterModelSmoothingTailConstant cp cs cy mu kappa
      (parameterSpatialTransferCoefficient Es Ey Bc T) T D m r
  let Cq := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d)
    mu kappa Bc T (fun j => T (j+1)) D 0 m r
  have hCg : 0 ≤ Cg := parameterModelSmoothingTailConstant_nonneg cp cs cy mu kappa
    (parameterSpatialTransferCoefficient_nonneg Es Ey hBc hT) hT D m r
  have hCq : 0 ≤ Cq := modelTensorSmoothingTailConstant_nonneg n (parameterTensorModelEquiv n d)
    mu kappa hBc hT (fun j => hT (j+1)) D 0 m r
  have hC : 0 ≤ max Cg Cq := hCg.trans (le_max_left _ _)
  have ht : 0 < t := (htau.trans_le htaul).trans_le helt
  have ha : 0 ≤ (ell/t)^r := pow_nonneg (div_nonneg (htau.trans_le htaul).le ht.le) _
  have hb : 0 ≤ (tau/t)^r := pow_nonneg (div_nonneg htau.le ht.le) _
  have hbudget' : (G r).toReal + (Q r).toReal ≤ budget := by
    rw [← ENNReal.toReal_add hGr hQr]
    exact hbudget
  refine ⟨hg.1, hq.1, ENNReal.add_ne_top.mpr ⟨hg.2.1,hq.2.1⟩, ?_⟩
  rw [round4ParameterSpatialPairWeighted, ENNReal.toReal_add hg.2.1 hq.2.1]
  calc
    _ ≤ Cg * ((G r).toReal*(ell/t)^r+(G m).toReal*(tau/t)^r) +
        Cq * ((Q r).toReal*(ell/t)^r+(Q m).toReal*(tau/t)^r) := add_le_add hg.2.2 hq.2.2
    _ ≤ max Cg Cq * ((G r).toReal*(ell/t)^r+(G m).toReal*(tau/t)^r) +
        max Cg Cq * ((Q r).toReal*(ell/t)^r+(Q m).toReal*(tau/t)^r) :=
      add_le_add (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (add_nonneg (mul_nonneg ENNReal.toReal_nonneg ha) (mul_nonneg ENNReal.toReal_nonneg hb)))
        (mul_le_mul_of_nonneg_right (le_max_right _ _)
          (add_nonneg (mul_nonneg ENNReal.toReal_nonneg ha) (mul_nonneg ENNReal.toReal_nonneg hb)))
    _ = max Cg Cq * (((G r).toReal+(Q r).toReal)*(ell/t)^r +
        ((G m).toReal+(Q m).toReal)*(tau/t)^r) := by ring
    _ ≤ max Cg Cq * (budget*(ell/t)^r +
        ((G m).toReal+(Q m).toReal)*(tau/t)^r) :=
      mul_le_mul_of_nonneg_left (add_le_add (mul_le_mul_of_nonneg_right hbudget' ha) le_rfl) hC
    _ = _ := by rw [round4ParameterSpatialPairWeighted, ENNReal.toReal_add hGm hQm]

#print axioms round4SpatialClosed_actual_pair_tail
end
end GlobalEmbedding.Continuation
