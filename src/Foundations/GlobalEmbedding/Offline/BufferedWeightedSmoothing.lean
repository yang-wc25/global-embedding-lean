import GlobalEmbedding.Offline.BufferedSmoothingEstimates
import GlobalEmbedding.Offline.BufferedSmoothingLinearity

/-!
# Global buffered smoothing in the original weighted atlas norm

Source: `main.tex` 700–720, equation (6.4) and its buffered localization.
This endpoint concerns the SAME actual manifold map assembled through the
original charts and square partition. All cutoff and chart-transition terms
are included. Input norms use fixed actual sampling buffers; output norms
use original inner domains. Both use the original coordinate norm definitions.

The explicit constants have no manifold, atlas, finite-index-type, source,
scale, or chart-count argument. Actual overlap multiplicity and uniform
cutoff/transition derivative sequences are retained as provider parameters.
Base two is the spatial map norm when every displayed coordinate is spatial;
parameter-spatial packets and tensor-frame transitions are not identified here.
-/

open MeasureTheory GlobalEmbedding.Paper Function Set Manifold
open scoped ContDiff Topology ENNReal BigOperators

namespace GlobalEmbedding.Offline

noncomputable section

/-- One explicit global tail constant. Its arguments contain no atlas or chart index. -/
def paperBufferedSmoothingTailConstant {d : ℕ} (mu : Measure (Fin d → ℝ))
    (kappa : (Fin d → ℝ) → ℝ) (B T : ℕ → ℝ) (D base m r : ℕ) : ℝ :=
  bufferedTransferConstant B T D (m + base) * paperShiftedSmoothingTailConstant mu kappa base m r

theorem paperBufferedSmoothingTailConstant_nonneg {d : ℕ} (mu : Measure (Fin d → ℝ))
    (kappa : (Fin d → ℝ) → ℝ) {B T : ℕ → ℝ} (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j)
    (D base m r : ℕ) : 0 ≤ paperBufferedSmoothingTailConstant mu kappa B T D base m r :=
  mul_nonneg (bufferedTransferConstant_nonneg hB hT D _) (paperShiftedSmoothingTailConstant_nonneg mu kappa _ _ _)

variable {d q : ℕ} {M : Type*} [TopologicalSpace M]
    [ChartedSpace (Fin d → ℝ) M] [IsManifold 𝓘(ℝ, Fin d → ℝ) ∞ M]

/-- The actual global two-term weighted tail. The proof derives both the
low Taylor and high signed-L1 profiles from source norms, after native global
chart/cutoff localization, then applies the proved finite weighted algebra. -/
theorem paperAtlasWeighted_buffered_smoothing_tail (A : BufferedAtlas M (Fin d → ℝ))
    (hA : IsSmoothBufferedAtlas A) (mu : Measure (Fin d → ℝ)) [mu.IsAddHaarMeasure]
    {kappa : (Fin d → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base m r : ℕ) {rho tau ell t : ℝ}
    (hsupp : tsupport (finiteMomentKernel r kappa) ⊆ Metric.ball 0 rho)
    (hrho : rho ≤ A.buffer) (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (chi : Fin A.count → M → ℝ)
    (hchi : ∀ i, ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, ℝ) ∞ (chi i))
    (hchiSupport : ∀ i, tsupport (chi i) ⊆ A.inner i)
    (hpartition : ∀ x, ∑ i, chi i x ^ 2 = 1)
    {u : M → Fin q → ℝ} (hu : ContMDiff 𝓘(ℝ, Fin d → ℝ) 𝓘(ℝ, Fin q → ℝ) ∞ u)
    (B T : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (hT : ∀ j, 0 ≤ T j) (D : ℕ)
    (hD : ∀ x, (activeCutoffIndices chi x).card ≤ D)
    (hweight : ∀ p i k, ∀ y ∈ bufferedInnerCoordinates A p, (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (chi i ∘ (A.chart p).symm) y‖ ≤ B k)
    (htransition : ∀ p i k, 1 ≤ k → ∀ y ∈ bufferedInnerCoordinates A p,
      (A.chart p).symm y ∈ tsupport (chi i) →
      ‖iteratedFDeriv ℝ k (A.chart i ∘ (A.chart p).symm) y‖ ≤ T k)
    (hNr : paperAtlasWeighted base r t (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤)
    (hNm : paperAtlasWeighted base m t (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A) ≠ ⊤)
    (budget : ℝ) (hbudget : (paperAtlasWeighted base r t (bufferedAtlasCoordinates A u)
      (fun i => (A.chart i).target) (bufferedSamplingCoordinates A)).toReal ≤ budget) :
    let K := finiteMomentKernel r kappa
    let e := bufferedAtlasCoordinates A (bufferedSmoothing A mu K ell chi u - u)
    let O := fun i => (A.chart i).target
    paperAtlasWeighted base m tau e O (bufferedInnerCoordinates A) ≠ ⊤ ∧
      (paperAtlasWeighted base m tau e O (bufferedInnerCoordinates A)).toReal ≤
        paperBufferedSmoothingTailConstant mu kappa B T D base m r *
          (budget * (ell / t) ^ r + (paperAtlasWeighted base m t (bufferedAtlasCoordinates A u)
            O (bufferedSamplingCoordinates A)).toReal * (tau / t) ^ r) := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let f := bufferedAtlasCoordinates A u
  let e := bufferedAtlasCoordinates A (bufferedSmoothing A mu K ell chi u - u)
  let O := fun i => (A.chart i).target
  let U := bufferedInnerCoordinates A
  let V := bufferedSamplingCoordinates A
  let I := fun a => (paperAtlasCj (a + base) f O V).toReal
  let E := fun a => (paperAtlasCj (a + base) e O U).toReal
  let Q := bufferedTransferConstant B T D (m + base)
  let L := Q * kernelTailConstant mu K r * coordinateDimensionFactor d (r + base)
  let H := Q * (1 + ∫ y, |K y| ∂mu) * coordinateDimensionFactor d (m + base)
  have hell : 0 < ell := htau.trans_le htaul
  have ht : 0 < t := hell.trans_le helt
  have hell1 : ell ≤ 1 := helt.trans ht1
  have hQ : 0 ≤ Q := bufferedTransferConstant_nonneg hB hT D _
  have hL : 0 ≤ L := mul_nonneg (mul_nonneg hQ (kernelTailConstant_nonneg mu K r))
    (coordinateDimensionFactor_nonneg d _)
  have hmassabs : 0 ≤ 1 + ∫ y, |K y| ∂mu :=
    add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))
  have hH : 0 ≤ H := mul_nonneg (mul_nonneg hQ hmassabs) (coordinateDimensionFactor_nonneg d _)
  have hO : ∀ i, IsOpen (O i) := fun i => (A.chart i).open_target
  have hVO : ∀ i, V i ⊆ O i := bufferedSampling_subset_target A
  have hUO : ∀ i, U i ⊆ O i := fun _ _ hy => hy.1
  have hf : ∀ i, ContDiffOn ℝ ∞ (f i) (O i) := bufferedAtlasCoordinates_contDiffOn A hA hu
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (O i) :=
    bufferedAtlasCoordinates_contDiffOn A hA
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
  have hhighRaw (a : ℕ) (ha : a ≤ m) := paperAtlasCj_buffered_error_high A hA mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r)
    hsupp hrho hell.le hell1 chi hchi hchiSupport hpartition hu B T hB hT D hD hweight htransition
    (a + base) (hfinM a ha)
  have houtC : paperAtlasCj (m + base) e O U ≠ ⊤ := (hhighRaw m le_rfl).1
  have houtBounded := (paperAtlasCj_ne_top_iff (m + base) e O U hO hUO he).mp houtC
  have hout : paperAtlasWeighted base m tau e O U ≠ ⊤ :=
    paperAtlasWeighted_ne_top base m tau e O U hO hUO he houtBounded
  have hlow : ∀ a ≤ m, a ≤ r → E a ≤ L * ell ^ (r - a) * I r := by
    intro a ha har
    have h := (paperAtlasCj_buffered_error_low A hA mu hsmooth hcompact hmass base r a har
      hsupp hrho hell.le hell1 chi hchi hchiSupport hpartition hu B T hB hT D hD hweight htransition hfinR).2
    apply h.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    apply mul_le_mul_of_nonneg_right _ (pow_nonneg hell.le _)
    apply mul_le_mul_of_nonneg_right _ (coordinateDimensionFactor_nonneg d _)
    exact mul_le_mul_of_nonneg_right
      (bufferedTransferConstant_mono hB hT D (Nat.add_le_add_right ha base)) (kernelTailConstant_nonneg mu K r)
  have hhigh : ∀ a ≤ m, E a ≤ H * I a := by
    intro a ha
    apply (hhighRaw a ha).2.trans
    apply mul_le_mul_of_nonneg_right _ ENNReal.toReal_nonneg
    exact mul_le_mul
      (mul_le_mul_of_nonneg_right
        (bufferedTransferConstant_mono hB hT D (Nat.add_le_add_right ha base)) hmassabs)
      (coordinateDimensionFactor_mono d (Nat.add_le_add_right ha base))
      (coordinateDimensionFactor_nonneg d _) (mul_nonneg hQ hmassabs)
  have hNrSum : (∑ a ∈ Finset.range (r + 1), t ^ a * I a) ≤ budget := by
    rw [paperAtlasWeighted_toReal base r t ht.le f O V hNr] at hbudget
    exact hbudget
  have hw := weighted_low_high_tail m r I E (fun _ => ENNReal.toReal_nonneg)
    L H hL hH htau.le htaul helt ht budget hNrSum hlow hhigh
  refine ⟨hout, ?_⟩
  rw [paperAtlasWeighted_toReal base m tau htau.le _ O U hout,
    paperAtlasWeighted_toReal base m t ht.le f O V hNm]
  convert hw using 1
  unfold paperBufferedSmoothingTailConstant paperShiftedSmoothingTailConstant
  dsimp only [L, H, Q, K]
  ring

end

end GlobalEmbedding.Offline
