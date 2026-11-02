import Smoothing.IntegrationSpatialModelNorms
import Smoothing.ParameterGlobalEstimates

/-!
# Original model coordinates of the actual global parameter map

The native global smoother is unchanged. This file supplies its true source
jets from the original anisotropic coordinate norm on the fixed sampling
buffer, and converts its actual low/high global error jets back to that norm.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function Filter MeasureTheory Manifold IsManifold
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
local notation "AB" => parameterProductAtlas A B

def parameterBufferedNativeCoordinates (u : P × M → Y) :
    Fin (B.count * A.count) → Ep × Es → Y := fun i => u ∘ ((AB).chart i).symm

def parameterBufferedModelCoordinates
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) (u : P × M → Y) :=
  parameterModelCoordinates cp cs cy (parameterBufferedNativeCoordinates A B u)

def parameterBufferedModelTargets
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ)) :=
  parameterModelDomains cp cs (fun i => ((AB).chart i).target)

def parameterBufferedModelSampling
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ)) :=
  parameterModelDomains cp cs (bufferedSamplingCoordinates AB)

def parameterBufferedModelInner
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ)) :=
  parameterModelDomains cp cs (bufferedInnerCoordinates AB)

theorem parameterBufferedNativeCoordinates_contDiffOn
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B) {u : P × M → Y}
    (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u) (i : Fin (B.count * A.count)) :
    ContDiffOn ℝ ∞ (parameterBufferedNativeCoordinates A B u i) ((AB).chart i).target := by
  letI : ChartedSpace (Ep × Es) (Ep × Es) := chartedSpaceSelf (Ep × Es)
  exact (hu.comp_contMDiffOn (contMDiffOn_symm_of_mem_maximalAtlas
    ((parameterProductAtlas_smooth A B hA hB).chart_mem i))).contDiffOn

/-- The original norm controls actual zero-extended spatial jets where the
kernel samples. Equality is a germ in the original open chart target. -/
theorem parameterBufferedSource_jet_le
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
    (cy : Y ≃L[ℝ] (Fin q → ℝ)) {u : P × M → Y}
    (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u) (j : ℕ)
    (hfinite : parameterSpatialCj (n := n) (d := d) j
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤)
    (i : Fin (B.count * A.count)) (k : ℕ) (hk : k ≤ j)
    (y : Ep × Es) (hy : y ∈ bufferedSamplingCoordinates AB i) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (bufferedCoordinateExtension AB u i)) y‖ ≤
      parameterModelNativeFactor cp cs cy j *
        (parameterSpatialCj (n := n) (d := d) j (parameterBufferedModelCoordinates A B cp cs cy u)
          (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs)).toReal := by
  have he := spatialNativeJet_eventuallyEq
    (bufferedCoordinateExtension_eventuallyEq AB u i (bufferedSampling_subset_target AB i hy))
  rw [(he.iteratedFDeriv ℝ k).eq_of_nhds]
  exact parameterModelCj_native_jet_le cp cs cy j (parameterBufferedNativeCoordinates A B u)
    (fun a => ((AB).chart a).target) (bufferedSamplingCoordinates AB)
    (fun a => ((AB).chart a).open_target) (bufferedSampling_subset_target AB)
    (parameterBufferedNativeCoordinates_contDiffOn A B hA hB hu) hfinite i hk hy

variable (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
  (cp : Ep ≃L[ℝ] (Fin d → ℝ)) (cs : Es ≃L[ℝ] (Fin n → ℝ))
  (cy : Y ≃L[ℝ] (Fin q → ℝ))
  (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]

include hA hB

/-- Actual global low Taylor estimate in the literal original anisotropic Cj
norm, keeping the native model, target, buffer and global map unchanged. -/
theorem parameterBufferedModel_error_low
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
    (hcoeff : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (parameterBufferedTransfer (Y := Y) A B chi p i) y‖ ≤ C k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates AB p,
      ((AB).chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k ((AB).chart i ∘ ((AB).chart p).symm) y‖ ≤ T k)
    (hfinite : parameterSpatialCj (n := n) (d := d) r
      (parameterBufferedModelCoordinates A B cp cs cy u)
      (parameterBufferedModelTargets A B cp cs) (parameterBufferedModelSampling A B cp cs) ≠ ⊤) :
    let S := bufferedSmoothing AB mu (finiteMomentKernel r kappa) ell chi u
    let f := parameterBufferedModelCoordinates A B cp cs cy u
    let e := parameterBufferedModelCoordinates A B cp cs cy (fun z => S z - u z)
    let O := parameterBufferedModelTargets A B cp cs
    parameterSpatialCj (n := n) (d := d) j e O (parameterBufferedModelInner A B cp cs) ≠ ⊤ ∧
    (parameterSpatialCj (n := n) (d := d) j e O (parameterBufferedModelInner A B cp cs)).toReal ≤
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
    (fun i => ((AB).chart i).target) (bufferedInnerCoordinates AB)
    (fun i => ((AB).chart i).open_target) (fun i y hy => hy.1) he R hR ?_
  · refine ⟨hb.1, ?_⟩
    convert hb.2 using 1 <;> first | rfl | ring
  intro p k hk z hz
  exact parameterBufferedSmoothing_spatial_low A B hA hB mu hsmooth hcompact hmass r j hjr
    hsupp hrho hell hell1 chi hchi hchiSupport hpartition hu C T hC hT D p hz.1
    (hD _) (fun i hi a _ => hcoeff p i a z hz hi)
    (fun i hi a ha _ => htransition p i a ha z hz hi) P0 hP0
    (parameterBufferedSource_jet_le A B hA hB cp cs cy hu r hfinite) hk

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.parameterBufferedSource_jet_le
#print axioms GlobalEmbedding.Continuation.parameterBufferedModel_error_low
