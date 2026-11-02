import Smoothing.TensorLocalModelEstimates

/-!
# Local weighted tensor smoothing on the actual original chart model

Source: `main.tex` 700–720, equation (6.4). The SAME actual bilinear tensor smoother
is constructed on the original model E. The original cumulative component
norms are evaluated on genuine linear-model coordinate presentations, retaining
both actual operator norms. Constants are explicit before every manifold,
atlas, chart count, field, or scale. Source norms use fixed sampling buffers.
The finite chart family has no cover field. The square partition holds only
on the open region W, and output is evaluated on the original inner domains
intersected with W. The full original two-term weighted estimate is proved
from actual local Taylor and signed-L1 estimates, without assuming its tail.
-/

open Module MeasureTheory GlobalEmbedding.Paper Function Set Manifold IsManifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false



variable {ι E M : Type*} [Fintype ι] [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d n : ℕ} {V : M → Type*} [∀ x, AddCommGroup (V x)] [∀ x, Module ℝ (V x)] [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual global tensor two-term weighted tail. The proof derives both the
low Taylor and high signed-L1 profiles from source norms, after native global
chart/cutoff localization, then applies the proved finite weighted algebra. -/
theorem paperAtlasWeighted_model_local_tensor_smoothing_tail (A : TensorBufferedChartFamily ι M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : ∀ i, A.chart i ∈ maximalAtlas 𝓘(ℝ, E) ∞ M) (mu : Measure E) [mu.IsAddHaarMeasure]
    {kappa : E → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base m r : ℕ) {rho tau ell t : ℝ}
    (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : ι → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (W : Set M) (hW : IsOpen W) (hpartition : ∀ x ∈ W, ∑ i, chi i x ^ 2 = 1)
    (b : ι → (x : M) → Basis (Fin n) ℝ (V x))
    (H : (x : M) → LinearMap.BilinForm ℝ (V x))
    (hH : ∀ i, ContDiffOn ℝ ∞ (tensorLocalCoefficientField A b H i ∘ (A.chart i).symm)
      (A.chart i).target)
    (hframe : ∀ p i a r, ContDiffOn ℝ ∞ (tensorLocalFrameTransition A b p i a r)
      (tensorLocalChartOverlap A p i))
    (B T J : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (hJ : ∀ j, 0 ≤ J j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ tensorLocalInner A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ tensorLocalInner A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hframeBound : ∀ p i a r k, ∀ y ∈ tensorLocalInner A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (tensorLocalFrameTransition A b p i a r) y‖ ≤ J k)
    (hNr : paperAtlasWeighted base r t (tensorLocalModelCoordinates A c b H)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤)
    (hNm : paperAtlasWeighted base m t (tensorLocalModelCoordinates A c b H)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted base r t (tensorLocalModelCoordinates A c b H)
      (tensorLocalModelTargets A c) (tensorLocalModelSampling A c)).toReal ≤ budget) :
    let K := finiteMomentKernel r kappa
    let e := modelCoordinateFamily c (tensorLocalErrorCoordinates A mu K ell chi b H)
    let O := tensorLocalModelTargets A c
    paperAtlasWeighted base m tau e O (tensorLocalModelEvaluation A c W) ≠ ⊤ ∧
      (paperAtlasWeighted base m tau e O (tensorLocalModelEvaluation A c W)).toReal ≤
        modelTensorSmoothingTailConstant n c mu kappa B T J D base m r *
          (budget * (ell / t) ^ r + (paperAtlasWeighted base m t (tensorLocalModelCoordinates A c b H)
            O (tensorLocalModelSampling A c)).toReal * (tau / t) ^ r) := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let f := tensorLocalModelCoordinates A c b H
  let e := modelCoordinateFamily c (tensorLocalErrorCoordinates A mu K ell chi b H)
  let O := tensorLocalModelTargets A c
  let U := tensorLocalModelEvaluation A c W
  let V := tensorLocalModelSampling A c
  let I := fun a => (paperAtlasCj (a + base) f O V).toReal
  let E := fun a => (paperAtlasCj (a + base) e O U).toReal
  let Q := modelTensorTransferConstant n c B T J D (m + base)
  let L := Q * kernelTailConstant mu K r * nativeCoordinateFactor c (r + base)
  let High := Q * (1 + ∫ y, |K y| ∂mu) * nativeCoordinateFactor c (m + base)
  have hell : 0 < ell := htau.trans_le htaul
  have ht : 0 < t := hell.trans_le helt
  have hell1 : ell ≤ 1 := helt.trans ht1
  have hQ : 0 ≤ Q := modelTensorTransferConstant_nonneg n c hB hT hJ D _
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hQ (kernelTailConstant_nonneg mu K r))
    (nativeCoordinateFactor_nonneg c _)
  have hmassabs : 0 ≤ 1 + ∫ y, |K y| ∂mu :=
    add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))
  have hHigh : 0 ≤ High := mul_nonneg (mul_nonneg hQ hmassabs) (nativeCoordinateFactor_nonneg c _)
  have hO : ∀ i, IsOpen (O i) := tensorLocalModelTargets_open A c
  have hVO : ∀ i, V i ⊆ O i := tensorLocalModelSampling_subset_target A c
  have hUO : ∀ i, U i ⊆ O i := tensorLocalModelEvaluation_subset_target A c W
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) := tensorLocalModelCoordinates_contDiffOn A c b H hH
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i) :=
    modelCoordinateFamily_contDiffOn c (fun p =>
      (tensorLocalFieldSmoothing_coordinates_contDiffOn A hA mu (finiteMomentKernel_contDiff hsmooth r)
        (finiteMomentKernel_hasCompactSupport hcompact r) hsupp hrho hell.le hell1
        chi hchi hchiSupport b H hH hframe p).sub (hH p))
  have hboundedM := (paperAtlasWeighted_ne_top_iff base m t ht f O V hO hVO hf).mp hNm
  have hboundedR := (paperAtlasWeighted_ne_top_iff base r t ht f O V hO hVO hf).mp hNr
  have hfinM : ∀ a ≤ m, paperAtlasCj (a + base) f O V ≠ ⊤ := by
    intro a ha
    apply (paperAtlasCj_ne_top_iff (a + base) f O V hO hVO hf).mpr
    intro i k hk
    exact hboundedM i k (by omega)
  have hfinR : paperAtlasCj (r + base) f O V ≠ ⊤ :=
    (paperAtlasCj_ne_top_iff (r + base) f O V hO hVO hf).mpr hboundedR
  have hhighRaw (a : ℕ) (ha : a ≤ m) := paperAtlasCj_model_local_tensor_error_high A c hA mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r)
    hsupp hrho hell.le hell1 chi hchi hchiSupport W hW hpartition b H hH hframe B T J hB hT hJ D hD hweight htransition hframeBound
    (a + base) (hfinM a ha)
  have houtC : paperAtlasCj (m + base) e O U ≠ ⊤ := (hhighRaw m le_rfl).1
  have houtBounded := (paperAtlasCj_ne_top_iff (m + base) e O U hO hUO he).mp houtC
  have hout : paperAtlasWeighted base m tau e O U ≠ ⊤ :=
    paperAtlasWeighted_ne_top base m tau e O U hO hUO he houtBounded
  have hlow : ∀ a ≤ m, a ≤ r → E a ≤ L * ell ^ (r - a) * I r := by
    intro a ha har
    have h := (paperAtlasCj_model_local_tensor_error_low A c hA mu hsmooth hcompact hmass base r a har
      hsupp hrho hell.le hell1 chi hchi hchiSupport W hW hpartition b H hH hframe B T J hB hT hJ D hD hweight htransition hframeBound hfinR).2
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hell.le _)
    apply mul_le_mul_of_nonneg_right _ (nativeCoordinateFactor_nonneg c _)
    exact mul_le_mul_of_nonneg_right
      (modelTensorTransferConstant_mono n c hB hT hJ D (Nat.add_le_add_right ha base)) (kernelTailConstant_nonneg mu K r)
  have hhigh : ∀ a ≤ m, E a ≤ High * I a := by
    intro a ha
    apply (hhighRaw a ha).2.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        (modelTensorTransferConstant_mono n c hB hT hJ D (Nat.add_le_add_right ha base)) hmassabs)
      (nativeCoordinateFactor_mono c (Nat.add_le_add_right ha base))
      (nativeCoordinateFactor_nonneg c _) (mul_nonneg hQ hmassabs)
  have hNrSum : (∑ a ∈ Finset.range (r + 1), t ^ a * I a) ≤ budget := by
    rw [paperAtlasWeighted_toReal base r t ht.le f O V hNr] at hbudget
    exact hbudget
  have hw := weighted_low_high_tail m r I E (fun _ => ENNReal.toReal_nonneg)
    L High hL hHigh htau.le htaul helt ht budget hNrSum hlow hhigh
  refine ⟨hout, ?_⟩
  rw [paperAtlasWeighted_toReal base m tau htau.le _ O U hout,
    paperAtlasWeighted_toReal base m t ht.le f O V hNm]
  convert hw using 1
  unfold modelTensorSmoothingTailConstant
  dsimp only [L, High, Q, K]
  ring

#print axioms paperAtlasWeighted_model_local_tensor_smoothing_tail

end
end GlobalEmbedding.Offline
