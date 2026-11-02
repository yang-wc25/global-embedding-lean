import GlobalEmbedding.Offline.PaperSmoothingEstimates
import GlobalEmbedding.Offline.WeightedTailAlgebra

/-!
# The two-term local smoothing tail in the original weighted atlas norm

Source: `literature/parallelizable-stable-plus-one/main.tex`, equation
(6.4), lines 704–719, and `repair-local-convolution-estimates`.

This is the ordinary-field part of (6.4), on every finite family of
buffered coordinate domains, using the exact original cumulative
`paperAtlasWeighted` maximum norm. The kernel is the actual signed
finite-moment construction. Its constants depend only on the fixed
template, derivative orders and coordinate dimension, not on the scale,
input, buffer domains or number of charts. No localization/gluing of
charts or spatial two-jet assembly is asserted by this theorem.
-/

open MeasureTheory GlobalEmbedding.Paper
open scoped BigOperators ContDiff ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

variable {d : ℕ} (mu : Measure (Fin d → ℝ))

/-- An explicit fixed-template constant for the two-term weighted tail.
It uses true signed-kernel absolute moments and the original finite
coordinate/Fréchet comparison factors. -/
def paperSmoothingTailConstant (kappa : (Fin d → ℝ) → ℝ) (m r : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) *
      (kernelTailConstant mu (finiteMomentKernel r kappa) r * coordinateDimensionFactor d r) +
    (1 + ∫ y, |finiteMomentKernel r kappa y| ∂mu) * coordinateDimensionFactor d m

/-- The explicit coefficient in the actual weighted estimate is
nonnegative without imposing positivity on the signed kernel. -/
theorem paperSmoothingTailConstant_nonneg (kappa : (Fin d → ℝ) → ℝ) (m r : ℕ) :
    0 ≤ paperSmoothingTailConstant mu kappa m r := by
  unfold paperSmoothingTailConstant
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (kernelTailConstant_nonneg mu _ r) (coordinateDimensionFactor_nonneg d r)))
    (mul_nonneg (add_nonneg zero_le_one
      (integral_nonneg fun y => abs_nonneg (finiteMomentKernel r kappa y)))
      (coordinateDimensionFactor_nonneg d m))

variable [mu.IsAddHaarMeasure]

/-- Equation (6.4) for the actual local smoothing of ordinary fields,
in the original cumulative finite-atlas coordinate norm.

The only input size assumptions are finiteness of the displayed
weighted norms and `N_r(t,u) ≤ B`. Source smoothness is local to the
open buffers, and the actual kernel segments must remain in them.
The conclusion explicitly proves output finiteness before its real
projection. All chart maxima and all source/parameter coordinates are
retained. The separate spatial two-jet and global gluing steps are not
part of this local theorem.
-/
theorem paperAtlasWeighted_smoothing_tail {ι : Type*} [Fintype ι] {q : ℕ}
    {kappa : (Fin d → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (m r : ℕ) (u : ι → (Fin d → ℝ) → Fin q → ℝ)
    (U V : ι → Set (Fin d → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U i ⊆ V i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (V i))
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t) (ht1 : t ≤ 1)
    (hsegments : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ s ∈ Set.Icc (0 : ℝ) 1, x - s • (ell • y) ∈ V i)
    (hNr : paperAtlasWeighted 0 r t u V V ≠ ⊤)
    (hNm : paperAtlasWeighted 0 m t u V V ≠ ⊤)
    (B : ℝ) (hB : (paperAtlasWeighted 0 r t u V V).toReal ≤ B) :
    let K := finiteMomentKernel r kappa
    let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
    paperAtlasWeighted 0 m tau e U U ≠ ⊤ ∧
      (paperAtlasWeighted 0 m tau e U U).toReal ≤
        paperSmoothingTailConstant mu kappa m r *
          (B * (ell / t) ^ r + (paperAtlasWeighted 0 m t u V V).toReal * (tau / t) ^ r) := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
  let I := fun a => (paperAtlasCj a u V V).toReal
  let A := fun a => (paperAtlasCj a e U U).toReal
  let L := kernelTailConstant mu K r * coordinateDimensionFactor d r
  let H := (1 + ∫ y, |K y| ∂mu) * coordinateDimensionFactor d m
  have hell : 0 < ell := htau.trans_le htaul
  have ht : 0 < t := hell.trans_le helt
  have hL : 0 ≤ L := mul_nonneg (kernelTailConstant_nonneg mu K r)
    (coordinateDimensionFactor_nonneg d r)
  have hmassabs : 0 ≤ 1 + ∫ y, |K y| ∂mu :=
    add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))
  have hH : 0 ≤ H := mul_nonneg hmassabs (coordinateDimensionFactor_nonneg d m)
  have hbuffer : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport K, x - ell • y ∈ V i := by
    intro i x hx y hy
    simpa only [one_smul] using hsegments i x hx y hy 1 (by simp)
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (U i) := by
    intro i
    exact (signedSmoothing_contDiffOn mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) (hU i) (hV i) (hu i) ell
      (hbuffer i)).sub ((hu i).mono (hUV i))
  have hboundedM := (paperAtlasWeighted_ne_top_iff 0 m t ht u V V hV
    (fun _ => Set.Subset.rfl) hu).mp hNm
  have hboundedR := (paperAtlasWeighted_ne_top_iff 0 r t ht u V V hV
    (fun _ => Set.Subset.rfl) hu).mp hNr
  have hfinM : ∀ a ≤ m, paperAtlasCj a u V V ≠ ⊤ := by
    intro a ha
    apply (paperAtlasCj_ne_top_iff a u V V hV (fun _ => Set.Subset.rfl) hu).mpr
    intro i k hk
    exact hboundedM i k (by omega)
  have hfinR : paperAtlasCj r u V V ≠ ⊤ := by
    apply (paperAtlasCj_ne_top_iff r u V V hV (fun _ => Set.Subset.rfl) hu).mpr
    intro i k hk
    exact hboundedR i k (by omega)
  have hhighRaw (a : ℕ) (ha : a ≤ m) := paperAtlasCj_smoothing_error_high_le mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r)
    u U V hU hV hUV hu ell hbuffer a (hfinM a ha)
  have houtC : paperAtlasCj m e U U ≠ ⊤ := (hhighRaw m le_rfl).1
  have houtBounded := (paperAtlasCj_ne_top_iff m e U U hU
    (fun _ => Set.Subset.rfl) he).mp houtC
  have hout : paperAtlasWeighted 0 m tau e U U ≠ ⊤ :=
    paperAtlasWeighted_ne_top 0 m tau e U U hU (fun _ => Set.Subset.rfl) he
      (fun i k hk => houtBounded i k (by omega))
  have hlow : ∀ a ≤ m, a ≤ r → A a ≤ L * ell ^ (r - a) * I r := by
    intro a _ har
    exact (paperAtlasCj_smoothing_error_low_le mu hsmooth hcompact hmass r u U V
      hU hV hUV hu hell.le (helt.trans ht1) hsegments a har hfinR).2
  have hhigh : ∀ a ≤ m, A a ≤ H * I a := by
    intro a ha
    exact (hhighRaw a ha).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left (coordinateDimensionFactor_mono d ha) hmassabs)
      ENNReal.toReal_nonneg)
  have hNrSum : (∑ a ∈ Finset.range (r + 1), t ^ a * I a) ≤ B := by
    rw [paperAtlasWeighted_toReal 0 r t ht.le u V V hNr] at hB
    simpa only [Nat.add_zero] using hB
  have hw := weighted_low_high_tail m r I A (fun _ => ENNReal.toReal_nonneg)
    L H hL hH htau.le htaul helt ht B hNrSum hlow hhigh
  refine ⟨hout, ?_⟩
  rw [paperAtlasWeighted_toReal 0 m tau htau.le _ U U hout,
    paperAtlasWeighted_toReal 0 m t ht.le u V V hNm]
  simpa only [Nat.add_zero, paperSmoothingTailConstant] using hw

end

end GlobalEmbedding.Offline
