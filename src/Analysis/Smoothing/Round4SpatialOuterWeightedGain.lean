import Smoothing.IntegrationParameterWeightedGain
import Smoothing.Round4SpatialOuterModelEstimates

/-!
# Weighted gain of the same actual global parameter map

Every fixed original spatial-C2/joint-Cm slow norm follows from the genuine
spatial-C2 input alone. The same kernel and smoothing operator serve all m.
The explicit finite constant precedes the atlas, field and small scales.
The source-only spatial base packet is deliberately explicit; this theorem
is not an equality with frozen paperAtlasWeighted 2 on joint coordinates.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function MeasureTheory Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators
namespace GlobalEmbedding.Continuation

variable {Ep Es P M Y : Type*}
  [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
  [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
  [MeasurableSpace Ep] [BorelSpace Ep] [MeasurableSpace Es] [BorelSpace Es]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]
  [TopologicalSpace P] [TopologicalSpace M]
  [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
  [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]
  {n d q : ℕ}

private local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
private local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

variable (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
  (Vout : Fin (B.count * A.count) → Set (Ep × Es))
  (hOut : ∀ i, Vout i ⊆ ((parameterProductAtlas A B).chart i).target)
  (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
  (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
  (cy : Y ≃L[ℝ] (Fin q → ℝ))
  (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]
local notation "AB" => parameterProductAtlas A B

include hA hB hOut

theorem round4SpatialOuter_original_weighted_gain
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K) (m : ℕ)
    {rho tau ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 < ell) (hell1 : ell ≤ 1) (htau : 0 ≤ tau) (htaul : tau ≤ ell)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hcoeff : ∀ p i k, ∀ y ∈ ((AB).chart p).target,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) y‖ ≤ C k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((AB).chart p).target,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) 0
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤) :
    let S := bufferedSmoothing AB mu K ell chi u
    let f := parameterBufferedModelCoordinates A B cp cs cy u
    let s := parameterBufferedModelCoordinates A B cp cs cy S
    let O := parameterBufferedModelTargets A B cp cs
    parameterSpatialWeighted (n := n) (d := d) m tau s O (parameterModelDomains cp cs Vout) ≠ ⊤ ∧
    (parameterSpatialWeighted (n := n) (d := d) m tau s O (parameterModelDomains cp cs Vout)).toReal ≤
      parameterModelSmoothingGainConstant cp cs cy mu K C T D m *
        (parameterSpatialCj (n := n) (d := d) 0 f O (parameterBufferedModelSampling A B cp cs)).toReal := by
  dsimp only
  let S := bufferedSmoothing AB mu K ell chi u
  let s := parameterBufferedModelCoordinates A B cp cs cy S
  let O := parameterBufferedModelTargets A B cp cs
  let U := parameterModelDomains cp cs Vout
  let I := (parameterSpatialCj (n := n) (d := d) 0
    (parameterBufferedModelCoordinates A B cp cs cy u) O (parameterBufferedModelSampling A B cp cs)).toReal
  let Q := fun j => parameterModelTransferConstant cp cs cy C T D j *
    kernelGainConstant mu K j * parameterModelNativeFactor cp cs cy 0
  have hQ : ∀ j, 0 ≤ Q j := fun j => mul_nonneg
    (mul_nonneg (parameterModelTransferConstant_nonneg cp cs cy hC hT D j)
      (kernelGainConstant_nonneg mu K j)) (parameterModelNativeFactor_nonneg cp cs cy 0)
  have hg (j : ℕ) := round4SpatialOuterModel_gain A B Vout hOut hA hB cp cs cy mu hK hcompact j
    hsupp hrho hell hell1 chi hchi hchiSupport hu C T hC hT D hD hcoeff htransition hfinite
  have hout := parameterSpatialWeighted_ne_top_of_Cj m tau s O U (fun j _ => (hg j).1)
  refine ⟨hout, ?_⟩
  rw [parameterSpatialWeighted_toReal m tau htau s O U hout]
  calc
    _ ≤ ∑ j ∈ Finset.range (m+1), tau ^ j * (Q j * (ell⁻¹)^j * I) := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_mul_of_nonneg_left (hg j).2 (pow_nonneg htau _)
    _ = ∑ j ∈ Finset.range (m+1), (Q j * I) * (tau / ell)^j := by
      apply Finset.sum_congr rfl
      intro j _
      rw [div_eq_mul_inv, mul_pow]
      ring
    _ ≤ ∑ j ∈ Finset.range (m+1), Q j * I := by
      apply Finset.sum_le_sum
      intro j _
      exact mul_le_of_le_one_right (mul_nonneg (hQ j) ENNReal.toReal_nonneg)
        (pow_le_one₀ (div_nonneg htau hell.le) ((div_le_one hell).mpr htaul))
    _ = _ := by rw [← Finset.sum_mul]; rfl

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4SpatialOuter_original_weighted_gain
