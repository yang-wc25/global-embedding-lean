import GlobalEmbedding.Offline.BufferedModelEstimates

/-!
# Global weighted smoothing on the actual original chart model

Source: `main.tex` 700–720, equation (6.4). The SAME global buffered smoother
is constructed on the original model E. The original cumulative component
norms are evaluated on genuine linear-model coordinate presentations, retaining
both actual operator norms. Constants are explicit before every manifold,
atlas, chart count, field, or scale. Source norms use fixed sampling buffers.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

section Constants

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [MeasurableSpace E] {d : ℕ}

/-- Explicit original-model global tail constant, including the two directions
of linear model transport. Its type has no atlas or finite index parameter. -/
def modelBufferedSmoothingTailConstant (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E)
    (kappa : E → ℝ) (B T : ℕ → ℝ) (D base m r : ℕ) : ℝ :=
  modelBufferedTransferConstant c B T D (m + base) *
    (((m + 1 : ℕ) : ℝ) * (kernelTailConstant mu (finiteMomentKernel r kappa) r *
      nativeCoordinateFactor c (r + base)) +
      (1 + ∫ y, |finiteMomentKernel r kappa y| ∂mu) * nativeCoordinateFactor c (m + base))

theorem modelBufferedSmoothingTailConstant_nonneg (c : E ≃L[ℝ] (Fin d → ℝ)) (mu : Measure E)
    (kappa : E → ℝ) {B T : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    (D base m r : ℕ) : 0 ≤ modelBufferedSmoothingTailConstant c mu kappa B T D base m r := by
  unfold modelBufferedSmoothingTailConstant
  exact mul_nonneg (modelBufferedTransferConstant_nonneg c hB hT D _)
    (add_nonneg (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (kernelTailConstant_nonneg mu _ _) (nativeCoordinateFactor_nonneg c _)))
      (mul_nonneg (add_nonneg zero_le_one (integral_nonneg fun _ => abs_nonneg _))
        (nativeCoordinateFactor_nonneg c _)))

end Constants

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    {d q : ℕ} [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℝ, E) ∞ M]

/-- The actual global two-term weighted tail. The proof derives both the
low Taylor and high signed-L1 profiles from source norms, after native global
chart/cutoff localization, then applies the proved finite weighted algebra. -/
theorem paperAtlasWeighted_model_buffered_smoothing_tail (A : BufferedAtlas M E) (c : E ≃L[ℝ] (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure E) [mu.IsAddHaarMeasure]
    {kappa : E → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base m r : ℕ) {rho tau ell t : ℝ}
    (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, E) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hNr : paperAtlasWeighted base r t (bufferedModelCoordinates A c u)
      (bufferedModelTargets A c) (bufferedModelSampling A c) ≠ ⊤)
    (hNm : paperAtlasWeighted base m t (bufferedModelCoordinates A c u)
      (bufferedModelTargets A c) (bufferedModelSampling A c) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted base r t (bufferedModelCoordinates A c u)
      (bufferedModelTargets A c) (bufferedModelSampling A c)).toReal ≤ budget) :
    let K := finiteMomentKernel r kappa
    let e := bufferedModelCoordinates A c (bufferedSmoothing A mu K ell chi u - u)
    let O := bufferedModelTargets A c
    paperAtlasWeighted base m tau e O (bufferedModelInner A c) ≠ ⊤ ∧
      (paperAtlasWeighted base m tau e O (bufferedModelInner A c)).toReal ≤
        modelBufferedSmoothingTailConstant c mu kappa B T D base m r *
          (budget * (ell / t) ^ r + (paperAtlasWeighted base m t (bufferedModelCoordinates A c u)
            O (bufferedModelSampling A c)).toReal * (tau / t) ^ r) := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let f := bufferedModelCoordinates A c u
  let e := bufferedModelCoordinates A c (bufferedSmoothing A mu K ell chi u - u)
  let O := bufferedModelTargets A c
  let U := bufferedModelInner A c
  let V := bufferedModelSampling A c
  let I := fun a => (paperAtlasCj (a + base) f O V).toReal
  let E := fun a => (paperAtlasCj (a + base) e O U).toReal
  let Q := modelBufferedTransferConstant c B T D (m + base)
  let L := Q * kernelTailConstant mu K r * nativeCoordinateFactor c (r + base)
  let H := Q * (1 + ∫ y, |K y| ∂mu) * nativeCoordinateFactor c (m + base)
  have hell : 0 < ell := htau.trans_le htaul
  have ht : 0 < t := hell.trans_le helt
  have hell1 : ell ≤ 1 := helt.trans ht1
  have hQ : 0 ≤ Q := modelBufferedTransferConstant_nonneg c hB hT D _
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hQ (kernelTailConstant_nonneg mu K r))
    (nativeCoordinateFactor_nonneg c _)
  have hmassabs : 0 ≤ 1 + ∫ y, |K y| ∂mu :=
    add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hQ hmassabs) (nativeCoordinateFactor_nonneg c _)
  have hO : ∀ i, IsOpen (O i) := bufferedModelTargets_open A c
  have hVO : ∀ i, V i ⊆ O i := bufferedModelSampling_subset_target A c
  have hUO : ∀ i, U i ⊆ O i := bufferedModelInner_subset_target A c
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) := bufferedModelCoordinates_contDiffOn A hA c hu
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i) :=
    bufferedModelCoordinates_contDiffOn A hA c
      ((bufferedSmoothing_contMDiff A hA mu (finiteMomentKernel_contDiff hsmooth r)
        (finiteMomentKernel_hasCompactSupport hcompact r) hsupp hrho hell.le hell1 chi hchi hchiSupport hu).sub hu)
  have hboundedM := (paperAtlasWeighted_ne_top_iff base m t ht f O V hO hVO hf).mp hNm
  have hboundedR := (paperAtlasWeighted_ne_top_iff base r t ht f O V hO hVO hf).mp hNr
  have hfinM : ∀ a ≤ m, paperAtlasCj (a + base) f O V ≠ ⊤ := by
    intro a ha
    apply (paperAtlasCj_ne_top_iff (a + base) f O V hO hVO hf).mpr
    intro i k hk
    exact hboundedM i k (by omega)
  have hfinR : paperAtlasCj (r + base) f O V ≠ ⊤ :=
    (paperAtlasCj_ne_top_iff (r + base) f O V hO hVO hf).mpr hboundedR
  have hhighRaw (a : ℕ) (ha : a ≤ m) := paperAtlasCj_model_buffered_error_high A c hA mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r)
    hsupp hrho hell.le hell1 chi hchi hchiSupport hpartition hu B T hB hT D hD hweight htransition
    (a + base) (hfinM a ha)
  have houtC : paperAtlasCj (m + base) e O U ≠ ⊤ := (hhighRaw m le_rfl).1
  have houtBounded := (paperAtlasCj_ne_top_iff (m + base) e O U hO hUO he).mp houtC
  have hout : paperAtlasWeighted base m tau e O U ≠ ⊤ :=
    paperAtlasWeighted_ne_top base m tau e O U hO hUO he houtBounded
  have hlow : ∀ a ≤ m, a ≤ r → E a ≤ L * ell ^ (r - a) * I r := by
    intro a ha har
    have h := (paperAtlasCj_model_buffered_error_low A c hA mu hsmooth hcompact hmass base r a har
      hsupp hrho hell.le hell1 chi hchi hchiSupport hpartition hu B T hB hT D hD hweight htransition hfinR).2
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hell.le _)
    apply mul_le_mul_of_nonneg_right _ (nativeCoordinateFactor_nonneg c _)
    exact mul_le_mul_of_nonneg_right
      (modelBufferedTransferConstant_mono c hB hT D (Nat.add_le_add_right ha base)) (kernelTailConstant_nonneg mu K r)
  have hhigh : ∀ a ≤ m, E a ≤ H * I a := by
    intro a ha
    apply (hhighRaw a ha).2.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        (modelBufferedTransferConstant_mono c hB hT D (Nat.add_le_add_right ha base)) hmassabs)
      (nativeCoordinateFactor_mono c (Nat.add_le_add_right ha base))
      (nativeCoordinateFactor_nonneg c _) (mul_nonneg hQ hmassabs)
  have hNrSum : (∑ a ∈ Finset.range (r + 1), t ^ a * I a) ≤ budget := by
    rw [paperAtlasWeighted_toReal base r t ht.le f O V hNr] at hbudget
    exact hbudget
  have hw := weighted_low_high_tail m r I E (fun _ => ENNReal.toReal_nonneg)
    L H hL hH htau.le htaul helt ht budget hNrSum hlow hhigh
  refine ⟨hout, ?_⟩
  rw [paperAtlasWeighted_toReal base m tau htau.le _ O U hout,
    paperAtlasWeighted_toReal base m t ht.le f O V hNm]
  convert hw using 1
  unfold modelBufferedSmoothingTailConstant
  dsimp only [L, H, Q, K]
  ring

end

end GlobalEmbedding.Offline
