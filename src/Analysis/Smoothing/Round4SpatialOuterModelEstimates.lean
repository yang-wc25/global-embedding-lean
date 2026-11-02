import Smoothing.IntegrationParameterModelHighGain

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

/-- Actual global low Taylor estimate in the literal original anisotropic Cj
norm, keeping the native model, target, buffer and global map unchanged. -/
theorem round4SpatialOuterModel_error_low
    {kappa : Ep × Es → ℝ} (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1) (r j : ℕ) (hjr : j ≤ r)
    {rho ell : ℝ} (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    (hpartition : ∀ z, ∑ i, chi i z ^ 2 = 1)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ)
    (hD : ∀ z, (activeCutoffIndices chi z).card ≤ D)
    (hcoeff : ∀ p i k, ∀ y ∈ ((AB).chart p).target,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) y‖ ≤ C k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((AB).chart p).target,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) r
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤) :
    let S := bufferedSmoothing AB mu (finiteMomentKernel r kappa) ell chi u
    let f := parameterBufferedModelCoordinates A B cp cs cy u
    let e := parameterBufferedModelCoordinates A B cp cs cy (fun z => S z - u z)
    let O := parameterBufferedModelTargets A B cp cs
    parameterSpatialCj (n := n) (d := d) j e O (parameterModelDomains cp cs Vout) ≠ ⊤ ∧
    (parameterSpatialCj (n := n) (d := d) j e O (parameterModelDomains cp cs Vout)).toReal ≤
      parameterModelCoordinateFactor cp cs cy j * parameterJetTransferConstant C T D j *
        kernelTailConstant mu (finiteMomentKernel r kappa) r * parameterModelNativeFactor cp cs cy r *
        ell ^ (r-j) * (parameterSpatialCj (n := n) (d := d) r f O
          (parameterBufferedModelSampling A B cp cs)).toReal := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let S := bufferedSmoothing AB mu K ell chi u
  let I := (parameterSpatialCj (n := n) (d := d) r (parameterBufferedModelCoordinates A B cp cs cy u)
    (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs)).toReal
  let P0 := parameterModelNativeFactor cp cs cy r * I
  have hP0 : 0 ≤ P0 := mul_nonneg (parameterModelNativeFactor_nonneg cp cs cy r) ENNReal.toReal_nonneg
  let R := parameterJetTransferConstant C T D j * kernelTailConstant mu K r * P0 * ell^(r-j)
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (mul_nonneg (parameterJetTransferConstant_nonneg hC hT D j)
      (kernelTailConstant_nonneg mu K r)) hP0) (pow_nonneg hell _)
  have hS := parameterProductSmoothing_contMDiff A B hA hB mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r)
    hsupp hrho hell hell1 chi hchi hchiSupport hu
  have he := parameterBufferedNativeCoordinates_contDiffOn A B hA hB (hS.sub hu)
  have hb := parameterModelCj_finite_and_bound_of_native cp cs cy j
    (parameterBufferedNativeCoordinates A B (fun z => S z - u z))
    (fun i => ((AB).chart i).target) Vout
    (fun i => ((AB).chart i).open_target) hOut he R hR ?_
  · refine ⟨hb.1, ?_⟩
    convert hb.2 using 1 <;> first | rfl | ring
  intro p k hk z hz
  exact parameterBufferedSmoothing_spatial_low A B hA hB mu hsmooth hcompact hmass r j hjr
    hsupp hrho hell hell1 chi hchi hchiSupport hpartition hu C T hC hT D p (hOut p hz)
    (hD _) (fun i hi a _ => hcoeff p i a z (hOut p hz) hi)
    (fun i hi a ha _ => htransition p i a ha z (hOut p hz) hi) P0 hP0
    (parameterBufferedSource_jet_le A B hA hB cp cs cy hu r hfinite) hk

/-- The actual signed-L1 high profile in original anisotropic coordinates. -/
theorem round4SpatialOuterModel_error_high
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
    (hcoeff : ∀ p i k, ∀ y ∈ ((AB).chart p).target,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) y‖ ≤ C k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ ((AB).chart p).target,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) j
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤) :
    let S := bufferedSmoothing AB mu K ell chi u
    let f := parameterBufferedModelCoordinates A B cp cs cy u
    let e := parameterBufferedModelCoordinates A B cp cs cy (fun z => S z - u z)
    let O := parameterBufferedModelTargets A B cp cs
    parameterSpatialCj (n := n) (d := d) j e O (parameterModelDomains cp cs Vout) ≠ ⊤ ∧
    (parameterSpatialCj (n := n) (d := d) j e O (parameterModelDomains cp cs Vout)).toReal ≤
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
    (fun i => ((AB).chart i).target) Vout
    (fun i => ((AB).chart i).open_target) hOut he R hR ?_
  · refine ⟨hb.1, ?_⟩
    convert hb.2 using 1 <;> first | rfl | ring
  intro p k hk z hz
  exact parameterBufferedSmoothing_spatial_high A B hA hB mu hK hcompact
    hsupp hrho hell hell1 chi hchi hchiSupport hpartition hu C T hC hT D j p (hOut p hz)
    (hD _) (fun i hi a _ => hcoeff p i a z (hOut p hz) hi)
    (fun i hi a ha _ => htransition p i a ha z (hOut p hz) hi) P0 hP0
    (parameterBufferedSource_jet_le A B hA hB cp cs cy hu j hfinite) hk

/-- The actual map's original spatial-C2/joint-Cj gain, with no parameter
derivative in the input and no new smoothing map selected for order j. -/
theorem round4SpatialOuterModel_gain
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K) (j : ℕ)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 < ell) (hell1 : ell ≤ 1)
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
    parameterSpatialCj (n := n) (d := d) j s O (parameterModelDomains cp cs Vout) ≠ ⊤ ∧
    (parameterSpatialCj (n := n) (d := d) j s O (parameterModelDomains cp cs Vout)).toReal ≤
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
    (fun i => ((AB).chart i).target) Vout
    (fun i => ((AB).chart i).open_target) hOut hs R hR ?_
  · refine ⟨hb.1, ?_⟩
    convert hb.2 using 1 <;> first | rfl | ring
  intro p k hk z hz
  exact parameterBufferedSmoothing_spatial_gain A B hA hB mu hK hcompact
    hsupp hrho hell hell1 chi hchi hchiSupport hu C T hC hT D j p (hOut p hz)
    (hD _) (fun i hi a _ => hcoeff p i a z (hOut p hz) hi)
    (fun i hi a ha _ => htransition p i a ha z (hOut p hz) hi) P0 hP0
    (parameterBufferedSource_jet_le A B hA hB cp cs cy hu 0 hfinite) hk

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.round4SpatialOuterModel_error_low
#print axioms GlobalEmbedding.Continuation.round4SpatialOuterModel_error_high
#print axioms GlobalEmbedding.Continuation.round4SpatialOuterModel_gain
