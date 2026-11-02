import Smoothing.ParameterGlobalGainJets
import GlobalEmbedding.Offline.BufferedSamplingDomains

/-!
# Genuine global low, high and derivative-gain estimates with parameters

These substitute proved compact-convolution estimates into the actual global
map's native spatial-jet localization. The source assumptions are ONLY bounds
on joint derivatives of the spatial two-jet on the fixed sampling buffer.
-/

open GlobalEmbedding.Offline GlobalEmbedding.Paper Function Filter Set MeasureTheory Manifold IsManifold
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation
noncomputable section

variable {Ep Es P M Y : Type*}
    [NormedAddCommGroup Ep] [NormedSpace ℝ Ep] [FiniteDimensional ℝ Ep]
    [NormedAddCommGroup Es] [NormedSpace ℝ Es] [FiniteDimensional ℝ Es]
    [MeasurableSpace Ep] [BorelSpace Ep] [MeasurableSpace Es] [BorelSpace Es]
    [TopologicalSpace P] [TopologicalSpace M]
    [ChartedSpace Ep P] [IsManifold 𝓘(ℝ, Ep) ∞ P]
    [ChartedSpace Es M] [IsManifold 𝓘(ℝ, Es) ∞ M]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y] [FiniteDimensional ℝ Y]

local instance : ChartedSpace (Ep × Es) (P × M) := prodChartedSpace Ep P Es M
local instance : IsManifold 𝓘(ℝ, Ep × Es) ∞ (P × M) := by
  rw [modelWithCornersSelf_prod]
  exact IsManifold.prod (I := 𝓘(ℝ, Ep)) (I' := 𝓘(ℝ, Es)) (n := ∞) P M
attribute [local instance] spatialNativeJetNormedAddCommGroup spatialNativeJetNormedSpace

variable (A : BufferedAtlas M Es) (B : BufferedAtlas P Ep)
    (hA : IsSmoothBufferedAtlas A) (hB : IsSmoothBufferedAtlas B)
    (mu : Measure (Ep × Es)) [mu.IsAddHaarMeasure]
local notation "AB" => parameterProductAtlas A B
include hA hB

/-- Global low Taylor profile for all additional joint derivatives through j. -/
theorem parameterBufferedSmoothing_spatial_low
    {kappa : Ep × Es → ℝ} (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1) (r j : ℕ) (hjr : j ≤ r)
    {rho ell : ℝ} (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ k, 0 ≤ C k) (hT : ∀ k, 0 ≤ T k) (D : ℕ)
    (p : Fin (B.count * A.count)) {z : Ep × Es} (hz : z ∈ ((AB).chart p).target)
    (hD : (activeCutoffIndices chi (((AB).chart p).symm z)).card ≤ D)
    (hcoeff : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ a ≤ j, ‖iteratedFDeriv ℝ a (parameterBufferedTransfer (Y := Y) A B chi p i) z‖ ≤ C a)
    (htransition : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ a, 1 ≤ a → a ≤ j → ‖iteratedFDeriv ℝ a ((AB).chart i ∘ ((AB).chart p).symm) z‖ ≤ T a)
    (P0 : ℝ) (hP0 : 0 ≤ P0)
    (hsource : ∀ i a, a ≤ r → ∀ y ∈ bufferedSamplingCoordinates AB i,
      ‖iteratedFDeriv ℝ a (spatialNativeJet (bufferedCoordinateExtension AB u i)) y‖ ≤ P0)
    {k : ℕ} (hk : k ≤ j) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (fun y =>
      bufferedSmoothing AB mu (finiteMomentKernel r kappa) ell chi u (((AB).chart p).symm y) -
        u (((AB).chart p).symm y))) z‖ ≤
      parameterJetTransferConstant C T D j * kernelTailConstant mu (finiteMomentKernel r kappa) r *
        P0 * ell^(r-j) := by
  let K := finiteMomentKernel r kappa
  let R := kernelTailConstant mu K r * P0 * ell^(r-j)
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelTailConstant_nonneg mu K r) hP0) (pow_nonneg hell _)
  have hAB := parameterProductAtlas_smooth A B hA hB
  have hlocal : ∀ i a, a ≤ j → ∀ y ∈ bufferedInnerCoordinates AB i,
      ‖iteratedFDeriv ℝ a (spatialNativeJet (bufferedLocalError AB mu K ell u i)) y‖ ≤ R := by
    intro i a ha y hy
    exact spatialNativeJet_local_low mu hsmooth hcompact hmass r j hjr
      (bufferedInnerCoordinates_open AB i) (bufferedSamplingCoordinates_open AB i)
      (bufferedInner_subset_sampling AB i)
      ((bufferedCoordinateExtension_contDiffOn AB hAB hu i).mono (bufferedSampling_subset_target AB i))
      hell (fun z hz w hw s hs => buffered_kernel_segment_mem_sampling AB i hsupp hrho hell hell1 hz hw hs)
      P0 hP0 (hsource i) ha hy
  have h := parameterBufferedSmoothing_spatial_jet_le A B hA hB mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r)
    hsupp hrho hell hell1 chi hchi hchiSupport hpartition hu C T hC hT D p hz hD
    j k hk R hR (fun i hi a ha => hcoeff i hi a (ha.trans hk))
    (fun i hi a ha haj => htransition i hi a ha (haj.trans hk))
    (fun i hi a ha => hlocal i a ha _ (bufferedInnerCoordinates_mem AB i (hchiSupport i hi)))
  exact h.trans_eq (by dsimp [R]; ring)

/-- Global high-order signed-L1 profile, with no pure parameter base derivatives. -/
theorem parameterBufferedSmoothing_spatial_high
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 ≤ ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ a, 0 ≤ C a) (hT : ∀ a, 0 ≤ T a) (D j : ℕ)
    (p : Fin (B.count * A.count)) {z : Ep × Es} (hz : z ∈ ((AB).chart p).target)
    (hD : (activeCutoffIndices chi (((AB).chart p).symm z)).card ≤ D)
    (hcoeff : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ a ≤ j, ‖iteratedFDeriv ℝ a (parameterBufferedTransfer (Y := Y) A B chi p i) z‖ ≤ C a)
    (htransition : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ a, 1 ≤ a → a ≤ j → ‖iteratedFDeriv ℝ a ((AB).chart i ∘ ((AB).chart p).symm) z‖ ≤ T a)
    (P0 : ℝ) (hP0 : 0 ≤ P0)
    (hsource : ∀ i a, a ≤ j → ∀ y ∈ bufferedSamplingCoordinates AB i,
      ‖iteratedFDeriv ℝ a (spatialNativeJet (bufferedCoordinateExtension AB u i)) y‖ ≤ P0)
    {k : ℕ} (hk : k ≤ j) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (fun y =>
      bufferedSmoothing AB mu K ell chi u (((AB).chart p).symm y) - u (((AB).chart p).symm y))) z‖ ≤
      parameterJetTransferConstant C T D j * (1 + ∫ y, |K y| ∂mu) * P0 := by
  let R := (1 + ∫ y, |K y| ∂mu) * P0
  have hR : 0 ≤ R := mul_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => abs_nonneg _)) hP0
  have hAB := parameterProductAtlas_smooth A B hA hB
  have hlocal : ∀ i a, a ≤ j → ∀ y ∈ bufferedInnerCoordinates AB i,
      ‖iteratedFDeriv ℝ a (spatialNativeJet (bufferedLocalError AB mu K ell u i)) y‖ ≤ R := by
    intro i a ha y hy
    apply spatialNativeJet_local_high mu hK hcompact
      (bufferedInnerCoordinates_open AB i) (bufferedSamplingCoordinates_open AB i)
      (bufferedInner_subset_sampling AB i)
      ((bufferedCoordinateExtension_contDiffOn AB hAB hu i).mono (bufferedSampling_subset_target AB i))
      ell _ a P0 (hsource i a ha) hy
    intro z hz w hw
    simpa only [one_smul] using buffered_kernel_segment_mem_sampling AB i hsupp hrho hell hell1 hz hw
      (s := 1) (by simp)
  have h := parameterBufferedSmoothing_spatial_jet_le A B hA hB mu hK hcompact
    hsupp hrho hell hell1 chi hchi hchiSupport hpartition hu C T hC hT D p hz hD
    j k hk R hR (fun i hi a ha => hcoeff i hi a (ha.trans hk))
    (fun i hi a ha haj => htransition i hi a ha (haj.trans hk))
    (fun i hi a ha => hlocal i a ha _ (bufferedInnerCoordinates_mem AB i (hchiSupport i hi)))
  exact h.trans_eq (by dsimp [R]; ring)

/-- The same actual global map has cumulative gain from its spatial C2 input. -/
theorem parameterBufferedSmoothing_spatial_gain
    {K : Ep × Es → ℝ} (hK : ContDiff ℝ ∞ K) (hcompact : HasCompactSupport K)
    {rho ell : ℝ} (hsupp : tsupport K ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ min B.buffer A.buffer) (hell : 0 < ell) (hell1 : ell ≤ 1)
    (chi : Fin (B.count * A.count) → P × M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ (AB).inner i)
    {u : P × M → Y} (hu : ContMDiff 𝓘(ℝ, Ep × Es) 𝓘(ℝ, Y) ∞ u)
    (C T : ℕ → ℝ) (hC : ∀ a, 0 ≤ C a) (hT : ∀ a, 0 ≤ T a) (D j : ℕ)
    (p : Fin (B.count * A.count)) {z : Ep × Es} (hz : z ∈ ((AB).chart p).target)
    (hD : (activeCutoffIndices chi (((AB).chart p).symm z)).card ≤ D)
    (hcoeff : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ a ≤ j, ‖iteratedFDeriv ℝ a (parameterBufferedTransfer (Y := Y) A B chi p i) z‖ ≤ C a)
    (htransition : ∀ i, ((AB).chart p).symm z ∈ tsupport (chi i) →
      ∀ a, 1 ≤ a → a ≤ j → ‖iteratedFDeriv ℝ a ((AB).chart i ∘ ((AB).chart p).symm) z‖ ≤ T a)
    (P0 : ℝ) (hP0 : 0 ≤ P0)
    (hsource : ∀ i a, a ≤ 0 → ∀ y ∈ bufferedSamplingCoordinates AB i,
      ‖iteratedFDeriv ℝ a (spatialNativeJet (bufferedCoordinateExtension AB u i)) y‖ ≤ P0)
    {k : ℕ} (hk : k ≤ j) :
    ‖iteratedFDeriv ℝ k (spatialNativeJet (fun y =>
      bufferedSmoothing AB mu K ell chi u (((AB).chart p).symm y))) z‖ ≤
      parameterJetTransferConstant C T D j * kernelGainConstant mu K j * P0 * (ell⁻¹)^j := by
  let R := kernelGainConstant mu K j * P0 * (ell⁻¹)^j
  have hR : 0 ≤ R := mul_nonneg (mul_nonneg (kernelGainConstant_nonneg mu K j) hP0)
    (pow_nonneg (inv_nonneg.mpr hell.le) _)
  have hAB := parameterProductAtlas_smooth A B hA hB
  have hlocal : ∀ i a, a ≤ j → ∀ y ∈ bufferedInnerCoordinates AB i,
      ‖iteratedFDeriv ℝ a (spatialNativeJet (bufferedLocalSmoothing AB mu K ell u i)) y‖ ≤ R := by
    intro i a ha y hy
    apply spatialNativeJet_local_cumulative_gain mu hK hcompact
      (bufferedInnerCoordinates_open AB i) (bufferedSamplingCoordinates_open AB i)
      ((bufferedCoordinateExtension_contDiffOn AB hAB hu i).mono (bufferedSampling_subset_target AB i))
      hell hell1 _ j P0 hP0 (hsource i) ha hy
    intro z hz w hw
    simpa only [one_smul] using buffered_kernel_segment_mem_sampling AB i hsupp hrho hell.le hell1 hz hw
      (s := 1) (by simp)
  have h := parameterBufferedSmoothing_gain_spatial_jet_le A B hA hB mu hK hcompact
    hsupp hrho hell.le hell1 chi hchi hchiSupport hu C T hC hT D p hz hD
    j k hk R hR (fun i hi a ha => hcoeff i hi a (ha.trans hk))
    (fun i hi a ha haj => htransition i hi a ha (haj.trans hk))
    (fun i hi a ha => hlocal i a ha _ (bufferedInnerCoordinates_mem AB i (hchiSupport i hi)))
  exact h.trans_eq (by dsimp [R]; ring)

#print axioms parameterBufferedSmoothing_spatial_low
#print axioms parameterBufferedSmoothing_spatial_high
#print axioms parameterBufferedSmoothing_spatial_gain

end
end GlobalEmbedding.Continuation
