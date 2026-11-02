import Smoothing.ParameterTotalGain
import Smoothing.TensorParameterSmoothing

/-!
# Literal original equation (6.4) with the frozen total-joint map norm

The map summand is exactly paperAtlasWeighted 2 in the original ABI; the
native source-tangent tensor summand is exactly paperAtlasWeighted 0.
One actual product atlas, one fixed signed kernel, one cutoff family and one
scale serve both fields. The single maximum constant precedes all atlases,
fields and scales. No anisotropic packet is substituted into the frozen norm.
The parameter atlas here is finite and covers all P.
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

local instance parameterTotalPairChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
local instance parameterTotalPairIsManifold : IsManifold
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

/-- The original S_m is precisely the sum of the original map total-joint base-two
norm and original tensor norm; this abbreviation changes neither summand. -/
def parameterOriginalTotalPairWeighted
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (u : P × M → Ey)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (m : ℕ) (t : ℝ) (S : Fin A.count × Fin B.count → Set (Fin (n+d) → ℝ)) : ℝ≥0∞ :=
  paperAtlasWeighted 2 m t (incrementsOriginalMapCoordinates A B.chart u)
    (incrementsOriginalDifferentiation A B.chart) S +
  paperAtlasWeighted 0 m t (incrementsOriginalTensorCoordinates A B.chart H)
    (incrementsOriginalDifferentiation A B.chart) S

/-- Equation (6.4) for the actual pair, with a single original input budget
and a single uniform constant, including finiteness before conversion to R. -/
theorem fixedKernel_original_parameter_total_pair_smoothing_tail
    (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (rho : ℝ) (hrho : 0 < rho) (hbuffer : rho ≤ min B.buffer A.buffer) (m r : ℕ)
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin (parameterProductAtlas A B).count → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (parameterProductAtlas A B).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Ey} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u)
    (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
      (incrementsOriginalDifferentiation A B.chart i))
    (Bc T : ℕ → ℝ) (hBc : ∀ j, 0 ≤ Bc j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ Bc k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates (parameterProductAtlas A B) p,
      ((parameterProductAtlas A B).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((parameterProductAtlas A B).chart i ∘ ((parameterProductAtlas A B).chart p).symm) y‖ ≤ T k)
    (hNr : parameterOriginalTotalPairWeighted A B u H r t (parameterTensorOriginalSampling A B) ≠ ⊤)
    (hNm : parameterOriginalTotalPairWeighted A B u H m t (parameterTensorOriginalSampling A B) ≠ ⊤)
    (budget : ℝ) (hbudget :
      (parameterOriginalTotalPairWeighted A B u H r t (parameterTensorOriginalSampling A B)).toReal ≤ budget) :
    let mu := (volume : Measure (Ep × Es))
    let K := fixedSmoothingKernel mu rho hrho r
    let kappa := normalizedSmoothingBase mu rho hrho
    let Cmap := modelBufferedSmoothingTailConstant (parameterTensorModelEquiv n d) mu kappa Bc T D 2 m r
    let Ctensor := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d)
      mu kappa Bc T (fun j => T (j+1)) D 0 m r
    let Su := bufferedSmoothing (parameterProductAtlas A B) mu K ell chi u
    let SH := parameterNativeTensorSmoothing A B hA mu K ell chi H
    ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ Su ∧
    (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
      (incrementsOriginalDifferentiation A B.chart i)) ∧
    parameterOriginalTotalPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
      m tau (parameterTensorOriginalInner A B) ≠ ⊤ ∧
    (parameterOriginalTotalPairWeighted A B (fun z => u z-Su z) (fun p x => H p x-SH p x)
      m tau (parameterTensorOriginalInner A B)).toReal ≤
      max Cmap Ctensor * (budget * (ell/t)^r +
        (parameterOriginalTotalPairWeighted A B u H m t (parameterTensorOriginalSampling A B)).toReal * (tau/t)^r) := by
  dsimp only
  let G (j : ℕ) := paperAtlasWeighted 2 j t
    (incrementsOriginalMapCoordinates A B.chart u) (incrementsOriginalDifferentiation A B.chart)
    (parameterTensorOriginalSampling A B)
  let Q (j : ℕ) := paperAtlasWeighted 0 j t (incrementsOriginalTensorCoordinates A B.chart H)
    (incrementsOriginalDifferentiation A B.chart) (parameterTensorOriginalSampling A B)
  have hGr : G r ≠ ⊤ := (ENNReal.add_ne_top.mp hNr).1
  have hQr : Q r ≠ ⊤ := (ENNReal.add_ne_top.mp hNr).2
  have hGm : G m ≠ ⊤ := (ENNReal.add_ne_top.mp hNm).1
  have hQm : Q m ≠ ⊤ := (ENNReal.add_ne_top.mp hNm).2
  have hg := fixedKernel_original_parameter_total_map_smoothing_tail A B hA hB rho hrho hbuffer m r
    htau htaul helt ht1 chi hchi hchiSupport hpartition hu Bc T hBc hT D hD hweight htransition
    hGr hGm (G r).toReal le_rfl
  have hq := fixedKernel_original_parameter_tensor_smoothing_tail A B hA hB rho hrho hbuffer m r
    htau htaul helt ht1 chi hchi hchiSupport hpartition H hH Bc T hBc hT D hD hweight htransition
    hQr hQm (Q r).toReal le_rfl
  dsimp only at hg hq
  let mu := (volume : Measure (Ep × Es))
  let kappa := normalizedSmoothingBase mu rho hrho
  let Cg := modelBufferedSmoothingTailConstant (parameterTensorModelEquiv n d) mu kappa Bc T D 2 m r
  let Cq := modelTensorSmoothingTailConstant n (parameterTensorModelEquiv n d)
    mu kappa Bc T (fun j => T (j+1)) D 0 m r
  have hCg : 0 ≤ Cg := modelBufferedSmoothingTailConstant_nonneg (parameterTensorModelEquiv n d) mu kappa hBc hT D 2 m r
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
  rw [parameterOriginalTotalPairWeighted, ENNReal.toReal_add hg.2.1 hq.2.1]
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
    _ = _ := by rw [parameterOriginalTotalPairWeighted, ENNReal.toReal_add hGm hQm]

#print axioms fixedKernel_original_parameter_total_pair_smoothing_tail
end
end GlobalEmbedding.Continuation
