import Smoothing.Round4SpatialPairFiniteConstants
import Smoothing.ParameterRound2CompactPair

/-!
# Literal parameter (6.4) on the same original compact sampling pieces

This theorem bounds all joint derivatives of the actual spatial value,
first derivative and Hessian, together with the original native tensor.
The source and output evaluation domains are the SAME compact Ω/Q pieces.
The smoothing maps, cutoffs, original coordinates and fixed kernel are the
ones used by the existing repair consumers. The single named constant reads
raw geometry only through m+2 and does not use either chart count.
-/

open GlobalEmbedding.Paper GlobalEmbedding.Offline Function Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

variable {n d N : ℕ} {M P : Type*} [TopologicalSpace M] [TopologicalSpace P]
    [ChartedSpace (EuclideanSpace ℝ (Fin n)) M]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) ∞ M]
    [ChartedSpace (EuclideanSpace ℝ (Fin d)) P]
    [IsManifold 𝓘(ℝ, EuclideanSpace ℝ (Fin d)) ∞ P]

private local instance round4SpatialPreparedGainChartedSpace : ChartedSpace
    (EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) (P × M) :=
  prodChartedSpace (EuclideanSpace ℝ (Fin d)) P (EuclideanSpace ℝ (Fin n)) M
private local instance round4SpatialPreparedGainIsManifold : IsManifold
    𝓘(ℝ, EuclideanSpace ℝ (Fin d) × EuclideanSpace ℝ (Fin n)) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin d)))
    (I' := 𝓘(ℝ, EuclideanSpace ℝ (Fin n))) (n := ∞) P M

local notation "Ep" => EuclideanSpace ℝ (Fin d)
local notation "Es" => EuclideanSpace ℝ (Fin n)
local notation "Ey" => EuclideanSpace ℝ (Fin N)

theorem round4_actual_spatial_prepared_gain_on_targets
    (BS₀ TS BP₀ TP : ℕ → ℝ)
    (hBS₀ : ∀ j, 0 ≤ BS₀ j) (hTS : ∀ j, 0 ≤ TS j)
    (hBP₀ : ∀ j, 0 ≤ BP₀ j) (hTP : ∀ j, 0 ≤ TP j) (Ds Dp : ℕ)
    (rho : ℝ) (hrho : 0 < rho) (m r : ℕ) :
    let C := round4SpatialPairConstant n d N rho hrho BS₀ TS BP₀ TP Ds Dp m r
    0 ≤ C ∧
      ∀ (pcount : ℕ) (A : BufferedAtlas M Es)
        (B : TensorBufferedChartFamily (Fin pcount) P Ep)
        (hA : IsSmoothBufferedAtlas A)
        (hB : ∀ i, B.chart i ∈ maximalAtlas 𝓘(ℝ, Ep) ∞ P)
        (RS : TensorRawCutoffPreparation A BS₀ TS Ds)
        (RP : TensorLocalRawPreparation B univ BP₀ TP Dp),
      rho ≤ min B.buffer A.buffer →
      ∀ (Omega : Fin A.count → Set Es) (Q : Fin pcount → Set Ep),
      (∀ i, IsCompact (Omega i)) → (∀ i, IsCompact (Q i)) →
      (∀ i, Omega i ⊆ (A.chart i).target) → (∀ i, Q i ⊆ (B.chart i).target) →
      (∀ i, bufferedSamplingCoordinates A i ⊆ Omega i) →
      (∀ i, tensorLocalSamplingCoordinates B i ⊆ Q i) →
      ∀ tau ell t : ℝ, 0 < tau → tau ≤ ell → ell ≤ t → t ≤ 1 →
      ∀ (u : P × M → Ey),
      ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ u →
      ∀ (H : (p : P) → (x : M) → LinearMap.BilinForm ℝ (TangentSpace 𝓘(ℝ, Es) x)),
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart H i)
        (incrementsOriginalDifferentiation A B.chart i)) →
      ∀ budget : ℝ,
      (round4ParameterSpatialPairWeighted A B u H r t
        (incrementsOriginalEvaluation A B.chart Omega Q univ)).toReal ≤ budget →
      let S := incrementsOriginalDifferentiation A B.chart
      let mu := (volume : Measure (Ep × Es))
      let K := fixedSmoothingKernel mu rho hrho r
      let chi := parameterLocalProductCutoff A B
        (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)
      let SF := parameterLocalMapSmoothing (parameterLocalProductFamily A B) mu K ell chi u
      let SH := tensorLocalParameterSmoothing A B hA mu K ell chi H
      ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Ey) ∞ SF ∧
      (∀ i, ContDiffOn ℝ ∞ (incrementsOriginalTensorCoordinates A B.chart SH i)
        (incrementsOriginalDifferentiation A B.chart i)) ∧
      round4ParameterSpatialPairWeighted A B SF SH
        m tau S ≠ ⊤ ∧
      (round4ParameterSpatialPairWeighted A B SF SH
        m tau S).toReal ≤ C * budget := by
  let Bc := round4ProductCutoffProfile BS₀ TS BP₀ TP Ds Dp
  let T := fun j => max (TP j) (TS j)
  let D := (Ds+1)*(Dp+1)
  have hBc : ∀ j, 0 ≤ Bc j := round4ProductCutoffProfile_nonneg hBS₀ hTS hBP₀ hTP Ds Dp
  have hT : ∀ j, 0 ≤ T j := fun j => (hTP j).trans (le_max_left _ _)
  let Ct := round4SpatialPairTailConstant n d N rho hrho BS₀ TS BP₀ TP Ds Dp m r
  let Cg := round4SpatialPairGainConstant n d N rho hrho BS₀ TS BP₀ TP Ds Dp m r
  have hCt : 0 ≤ Ct := (parameterModelSmoothingTailConstant_nonneg
    (EuclideanSpace.equiv (Fin d) ℝ) (EuclideanSpace.equiv (Fin n) ℝ)
    (EuclideanSpace.equiv (Fin N) ℝ) (volume : Measure (Ep × Es))
    (normalizedSmoothingBase (volume : Measure (Ep × Es)) rho hrho)
    (parameterSpatialTransferCoefficient_nonneg Es Ey hBc hT) hT D m r).trans (le_max_left _ _)
  have hCg : 0 ≤ Cg := (parameterModelSmoothingGainConstant_nonneg
    (EuclideanSpace.equiv (Fin d) ℝ) (EuclideanSpace.equiv (Fin n) ℝ)
    (EuclideanSpace.equiv (Fin N) ℝ) (volume : Measure (Ep × Es))
    (fixedSmoothingKernel (volume : Measure (Ep × Es)) rho hrho r)
    (parameterSpatialTransferCoefficient_nonneg Es Ey hBc hT) hT D m).trans (le_max_left _ _)
  refine ⟨hCt.trans (le_max_left _ _), ?_⟩
  intro pcount A B hA hB RS RP hbuffer Omega Q hOmega hQ hOmegaTarget hQTarget
    hsource hparameter tau ell t htau htaul helt ht1 u hu H hH budget hbudget
  have hcover := round4ClosedParameterRaw_cover B RP
  have huOrig := parameterOriginalMapCoordinates_contDiffOn A (round4ClosedParameterAtlas B hcover)
    hA (round4ClosedParameterAtlas_smooth B hcover hB) hu
  have ht : 0 < t := htau.trans_le (htaul.trans helt)
  have hell : 0 < ell := htau.trans_le htaul
  have hbudget0 : 0 ≤ budget := ENNReal.toReal_nonneg.trans hbudget
  have hfull (j : ℕ) := round4ParameterSpatialPairWeighted_finite
    A B Omega Q hOmega hQ hOmegaTarget hQTarget u huOrig H hH j t
  have hdomains : ∀ i, tensorLocalOriginalSampling A B i ⊆
      incrementsOriginalEvaluation A B.chart Omega Q univ i := by
    intro i y hy
    exact ⟨hy.1, hsource i.1 hy.2.1, hparameter i.2 hy.2.2.1, mem_univ _⟩
  have hle (j : ℕ) : round4ParameterSpatialPairWeighted A B u H j t (tensorLocalOriginalSampling A B) ≤
      round4ParameterSpatialPairWeighted A B u H j t
        (incrementsOriginalEvaluation A B.chart Omega Q univ) :=
    add_le_add (parameterSpatialWeighted_mono_evaluation _ _ _ _ _ _ hdomains)
      (paperAtlasWeighted_mono_evaluation _ _ _ _ _ _ _ hdomains)
  have hsfinite (j : ℕ) := ne_top_of_le_ne_top (hfull j) (hle j)
  have hsle (j : ℕ) := ENNReal.toReal_mono (hfull j) (hle j)
  have hbase := add_le_add (parameterPaperAtlasCj_base_le_weighted 0 r t
      (parameterSpatialPacket (n := n) (d := d) (incrementsOriginalMapCoordinates A B.chart u))
      (fun iw => incrementsOriginalDifferentiation A B.chart iw.1)
      (fun iw => tensorLocalOriginalSampling A B iw.1))
    (parameterPaperAtlasCj_base_le_weighted 0 r t
      (incrementsOriginalTensorCoordinates A B.chart H) (incrementsOriginalDifferentiation A B.chart)
      (tensorLocalOriginalSampling A B))
  have hbasefinite := ne_top_of_le_ne_top (hsfinite r) hbase
  have hbasebudget := (ENNReal.toReal_mono (hsfinite r) hbase).trans ((hsle r).trans hbudget)
  obtain ⟨W, hW, hUW, hchi, hpart, hsupp, hD, hw, htrans⟩ :=
    round4_actual_product_smoothing_providers BS₀ TS BP₀ TP hBS₀ hTS hBP₀ hTP
      Ds Dp pcount A B hA hB univ RS RP
  have hpartAll : ∀ z : P × M, ∑ i, (parameterLocalProductCutoff A B
      (squareNormalizedCutoff RS.raw) (tensorLocalNormalizedCutoff RP.raw)) i z ^ 2 = 1 :=
    fun z => hpart z (hUW (mem_univ z.1))
  have hgresult := round4SpatialClosed_actual_pair_gain A B hcover hA hB rho hrho hbuffer m r
    hell (helt.trans ht1) htau.le htaul _ hchi hsupp hpartAll hu H hH Bc T hBc hT D hD hw htrans
    hbasefinite budget hbasebudget
  exact ⟨hgresult.1, hgresult.2.1, hgresult.2.2.1,
    hgresult.2.2.2.trans (mul_le_mul_of_nonneg_right (le_max_right Ct Cg) hbudget0)⟩

#print axioms round4_actual_spatial_prepared_gain_on_targets
end
end GlobalEmbedding.Continuation
