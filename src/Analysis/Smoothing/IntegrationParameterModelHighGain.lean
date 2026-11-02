import Smoothing.IntegrationParameterModelJets

/-!
# Original-model high and genuine spatial-C2 gain profiles

Both bounds concern the actual global map, in the original parameter/source
model and target. The source C0 packet contains only spatial derivatives up
to order two; no pure parameter derivative is added to the gain input.
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

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

variable (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
  (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
  (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
  (cy : Y ≃L[ℝ] (Fin q → ℝ))
  (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]
local notation "AB" => parameterProductAtlas A B

include hA hB

/-- The actual signed-L1 high profile in original anisotropic coordinates. -/
theorem parameterBufferedModel_error_high
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K) (j : ℕ)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hcoeff : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) y‖ ≤ C k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) j
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤) :
    let S := bufferedSmoothing AB mu K ell chi u
    let f := parameterBufferedModelCoordinates A B cp cs cy u
    let e := parameterBufferedModelCoordinates A B cp cs cy (fun z => S z - u z)
    let O := parameterBufferedModelTargets A B cp cs
    parameterSpatialCj (n := n) (d := d) j e O (parameterBufferedModelInner A B cp cs) ≠ ⊤ ∧
    (parameterSpatialCj (n := n) (d := d) j e O (parameterBufferedModelInner A B cp cs)).toReal ≤
      parameterModelCoordinateFactor cp cs cy j * parameterJetTransferConstant C T D j *
        (1 + ∫ y, |K y| ∂mu) * parameterModelNativeFactor cp cs cy j *
        (parameterSpatialCj (n := n) (d := d) j f O (parameterBufferedModelSampling A B cp cs)).toReal := by
  dsimp only
  let S := bufferedSmoothing AB mu K ell chi u
  let I := (parameterSpatialCj (n := n) (d := d) j (parameterBufferedModelCoordinates A B cp cs cy u)
    (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs)).toReal
  let P0 := parameterModelNativeFactor cp cs cy j * I
  have hP0 : 0 ≤ P0 := mul_nonneg (parameterModelNativeFactor_nonneg cp cs cy j) ENNReal.toReal_nonneg
  let R := parameterJetTransferConstant C T D j * (1 + ∫ y, |K y| ∂mu) * P0
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (parameterJetTransferConstant_nonneg hC hT D j)
      (add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y)))) hP0
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu hK hcompact
    hsupp hrho hell hell1 chi hchi hchiSupport hu
  have he := parameterBufferedNativeCoordinates_contDiffOn A B hA hB (hS.sub hu)
  have hb := parameterModelCj_finite_and_bound_of_native cp cs cy j
    (parameterBufferedNativeCoordinates A B (fun z => S z - u z))
    (fun i => ((AB).chart i).target) (bufferedInnerCoordinates AB)
    (fun i => ((AB).chart i).open_target) (fun i y hy => hy.1) he R hR ?_
  · refine ⟨hb.1, ?_⟩
    convert hb.2 using 1 <;> first | rfl | ring
  intro p k hk z hz
  exact parameterBufferedSmoothing_spatial_high A B hA hB mu hK hcompact
    hsupp hrho hell hell1 chi hchi hchiSupport hpartition hu C T hC hT D j p hz.1
    (hD _) (fun i hi a _ => hcoeff p i a z hz hi)
    (fun i hi a ha _ => htransition p i a ha z hz hi) P0 hP0
    (parameterBufferedSource_jet_le A B hA hB cp cs cy hu j hfinite) hk

/-- The actual map's original spatial-C2/joint-Cj gain, with no parameter
derivative in the input and no new smoothing map selected for order j. -/
theorem parameterBufferedModel_gain
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K) (j : ℕ)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hcoeff : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) y‖ ≤ C k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) 0
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤) :
    let S := bufferedSmoothing AB mu K ell chi u
    let f := parameterBufferedModelCoordinates A B cp cs cy u
    let s := parameterBufferedModelCoordinates A B cp cs cy S
    let O := parameterBufferedModelTargets A B cp cs
    parameterSpatialCj (n := n) (d := d) j s O (parameterBufferedModelInner A B cp cs) ≠ ⊤ ∧
    (parameterSpatialCj (n := n) (d := d) j s O (parameterBufferedModelInner A B cp cs)).toReal ≤
      parameterModelCoordinateFactor cp cs cy j * parameterJetTransferConstant C T D j *
        kernelGainConstant mu K j * parameterModelNativeFactor cp cs cy 0 * (ell⁻¹)^j *
        (parameterSpatialCj (n := n) (d := d) 0 f O (parameterBufferedModelSampling A B cp cs)).toReal := by
  dsimp only
  let S := bufferedSmoothing AB mu K ell chi u
  let I := (parameterSpatialCj (n := n) (d := d) 0 (parameterBufferedModelCoordinates A B cp cs cy u)
    (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs)).toReal
  let P0 := parameterModelNativeFactor cp cs cy 0 * I
  have hP0 : 0 ≤ P0 := mul_nonneg (parameterModelNativeFactor_nonneg cp cs cy 0) ENNReal.toReal_nonneg
  let R := parameterJetTransferConstant C T D j * kernelGainConstant mu K j * P0 * (ell⁻¹)^j
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (mul_nonneg (parameterJetTransferConstant_nonneg hC hT D j)
      (kernelGainConstant_nonneg mu K j)) hP0) (pow_nonneg (inv_nonneg.mpr hell.le) j)
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu hK hcompact
    hsupp hrho hell.le hell1 chi hchi hchiSupport hu
  have hs := parameterBufferedNativeCoordinates_contDiffOn A B hA hB hS
  have hb := parameterModelCj_finite_and_bound_of_native cp cs cy j
    (parameterBufferedNativeCoordinates A B S)
    (fun i => ((AB).chart i).target) (bufferedInnerCoordinates AB)
    (fun i => ((AB).chart i).open_target) (fun i y hy => hy.1) hs R hR ?_
  · refine ⟨hb.1, ?_⟩
    convert hb.2 using 1 <;> first | rfl | ring
  intro p k hk z hz
  exact parameterBufferedSmoothing_spatial_gain A B hA hB mu hK hcompact
    hsupp hrho hell hell1 chi hchi hchiSupport hu C T hC hT D j p hz.1
    (hD _) (fun i hi a _ => hcoeff p i a z hz hi)
    (fun i hi a ha _ => htransition p i a ha z hz hi) P0 hP0
    (parameterBufferedSource_jet_le A B hA hB cp cs cy hu 0 hfinite) hk

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.parameterBufferedModel_error_high
#print axioms GlobalEmbedding.Continuation.parameterBufferedModel_gain
