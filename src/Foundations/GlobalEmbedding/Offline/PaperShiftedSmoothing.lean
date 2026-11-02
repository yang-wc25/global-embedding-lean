import GlobalEmbedding.Offline.PaperSmoothingEstimates
import GlobalEmbedding.Offline.WeightedTailAlgebra

/-!
# The actual weighted smoothing tail with a fixed total derivative shift

Source: `literature/parallelizable-stable-plus-one/main.tex`, equation
(6.4), lines 704–719. For an unparameterized map, `base = 2` is its
genuine spatial two-jet shift because every coordinate is spatial.
For a parameter product, this theorem still refers to total C^(j+base)
and does not identify that norm with spatial-two-jet followed by total-j
derivatives. That separate restriction must be supplied explicitly.

The same order-r signed moment kernel works for every fixed base: Taylor
is applied to each existing output jet to degree r-j-1. No additional
moments through r+base or higher source derivative assumptions are used.
-/

open MeasureTheory GlobalEmbedding.Paper
open scoped BigOperators ContDiff ENNReal

namespace GlobalEmbedding.Offline

noncomputable section

variable {d q : ℕ} (mu : Measure (Fin d → ℝ)) [mu.IsAddHaarMeasure]

/-- Low-order bound for the genuine original cumulative C^(j+base)
norm, using only the input C^(r+base) norm and order-r kernel moments. -/
theorem paperAtlasCj_smoothing_error_shifted_low_le {ι : Type*} [Fintype ι]
    {kappa : (Fin d → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base r j : ℕ) (hjr : j ≤ r)
    (u : ι → (Fin d → ℝ) → Fin q → ℝ) (U V : ι → Set (Fin d → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U i ⊆ V i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (V i)) {ell : ℝ} (hell : 0 ≤ ell)
    (hsegments : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, x - t • (ell • y) ∈ V i)
    (hfinite : paperAtlasCj (r + base) u V V ≠ ⊤) :
    let K := finiteMomentKernel r kappa
    let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
    paperAtlasCj (j + base) e U U ≠ ⊤ ∧
      (paperAtlasCj (j + base) e U U).toReal ≤
        (kernelTailConstant mu K r * coordinateDimensionFactor d (r + base)) *
          ell ^ (r - j) * (paperAtlasCj (r + base) u V V).toReal := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
  let B := coordinateDimensionFactor d (r + base) * (paperAtlasCj (r + base) u V V).toReal
  let R := kernelTailConstant mu K r * B * ell ^ (r - j)
  have hB0 : 0 ≤ B := mul_nonneg (coordinateDimensionFactor_nonneg d (r + base)) ENNReal.toReal_nonneg
  have hR : 0 ≤ R := mul_nonneg
    (mul_nonneg (kernelTailConstant_nonneg mu K r) hB0) (pow_nonneg hell _)
  have hbuffer : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport K, x - ell • y ∈ V i := by
    intro i x hx y hy
    simpa only [one_smul] using hsegments i x hx y hy 1 (by simp)
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (U i) := by
    intro i
    exact (signedSmoothing_contDiffOn mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) (hU i) (hV i) (hu i) ell
      (hbuffer i)).sub ((hu i).mono (hUV i))
  have hbound : ∀ i, ∀ k ≤ j + base, ∀ x ∈ U i, ‖iteratedFDeriv ℝ k (e i) x‖ ≤ R := by
    intro i k hk x hx
    exact signedSmoothing_low_shifted_derivative_error_le mu hsmooth hcompact hmass base r j hjr
      (hU i) (hV i) (hUV i) (hu i) hell (hsegments i) B hB0
      (fun a ha z hz => paperAtlasCj_jet_le (r + base) u V V hV (fun _ => Set.Subset.rfl)
        hu hfinite i ha hz) hk hx
  have hle := paperAtlasCj_le_of_jet_bound (j + base) e U U hU
    (fun _ => Set.Subset.rfl) he R hbound
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hle
  refine ⟨hfin, ?_⟩
  have hreal := (ENNReal.toReal_le_toReal hfin ENNReal.ofReal_ne_top).mpr hle
  rw [ENNReal.toReal_ofReal hR] at hreal
  convert hreal using 1
  dsimp [R, B]
  ring

omit [mu.IsAddHaarMeasure] in
/-- The explicit fixed-template weighted-tail constant for total base
shift. Its value is independent of the number of chart labels. -/
def paperShiftedSmoothingTailConstant (kappa : (Fin d → ℝ) → ℝ) (base m r : ℕ) : ℝ :=
  ((m + 1 : ℕ) : ℝ) *
      (kernelTailConstant mu (finiteMomentKernel r kappa) r * coordinateDimensionFactor d (r + base)) +
    (1 + ∫ y, |finiteMomentKernel r kappa y| ∂mu) * coordinateDimensionFactor d (m + base)

omit [mu.IsAddHaarMeasure] in
/-- The shifted fixed-template constant is nonnegative, despite the
kernel being signed. -/
theorem paperShiftedSmoothingTailConstant_nonneg (kappa : (Fin d → ℝ) → ℝ) (base m r : ℕ) :
    0 ≤ paperShiftedSmoothingTailConstant mu kappa base m r := by
  unfold paperShiftedSmoothingTailConstant
  exact add_nonneg
    (mul_nonneg (Nat.cast_nonneg _)
      (mul_nonneg (kernelTailConstant_nonneg mu _ r)
        (coordinateDimensionFactor_nonneg d (r + base))))
    (mul_nonneg (add_nonneg zero_le_one
      (integral_nonneg fun y => abs_nonneg (finiteMomentKernel r kappa y)))
      (coordinateDimensionFactor_nonneg d (m + base)))

/-- The two-term weighted tail with a fixed total shift, in the exact
original `paperAtlasWeighted base` norm. For base2 and no parameter
coordinates this is the genuine map two-jet part of (6.4). In parameter
products it remains a total-shift theorem, with no spatial-only claim.
Output finiteness is explicitly proved. -/
theorem paperAtlasWeighted_smoothing_tail_totalShift {ι : Type*} [Fintype ι]
    {kappa : (Fin d → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (base m r : ℕ) (u : ι → (Fin d → ℝ) → Fin q → ℝ)
    (U V : ι → Set (Fin d → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U i ⊆ V i)
    (hu : ∀ i, ContDiffOn ℝ ∞ (u i) (V i))
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t)
    (hsegments : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ s ∈ Set.Icc (0 : ℝ) 1, x - s • (ell • y) ∈ V i)
    (hNr : paperAtlasWeighted base r t u V V ≠ ⊤)
    (hNm : paperAtlasWeighted base m t u V V ≠ ⊤)
    (B : ℝ) (hB : (paperAtlasWeighted base r t u V V).toReal ≤ B) :
    let K := finiteMomentKernel r kappa
    let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
    paperAtlasWeighted base m tau e U U ≠ ⊤ ∧
      (paperAtlasWeighted base m tau e U U).toReal ≤
        paperShiftedSmoothingTailConstant mu kappa base m r *
          (B * (ell / t) ^ r + (paperAtlasWeighted base m t u V V).toReal * (tau / t) ^ r) := by
  dsimp only
  let K := finiteMomentKernel r kappa
  let e := fun i x => signedSmoothing mu K ell (u i) x - u i x
  let I := fun a => (paperAtlasCj (a + base) u V V).toReal
  let A := fun a => (paperAtlasCj (a + base) e U U).toReal
  let L := kernelTailConstant mu K r * coordinateDimensionFactor d (r + base)
  let H := (1 + ∫ y, |K y| ∂mu) * coordinateDimensionFactor d (m + base)
  have hell : 0 < ell := htau.trans_le htaul
  have ht : 0 < t := hell.trans_le helt
  have hL : 0 ≤ L := mul_nonneg (kernelTailConstant_nonneg mu K r)
    (coordinateDimensionFactor_nonneg d (r + base))
  have hmassabs : 0 ≤ 1 + ∫ y, |K y| ∂mu :=
    add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))
  have hH : 0 ≤ H := mul_nonneg hmassabs (coordinateDimensionFactor_nonneg d (m + base))
  have hbuffer : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport K, x - ell • y ∈ V i := by
    intro i x hx y hy
    simpa only [one_smul] using hsegments i x hx y hy 1 (by simp)
  have he : ∀ i, ContDiffOn ℝ ∞ (e i) (U i) := by
    intro i
    exact (signedSmoothing_contDiffOn mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) (hU i) (hV i) (hu i) ell
      (hbuffer i)).sub ((hu i).mono (hUV i))
  have hboundedM := (paperAtlasWeighted_ne_top_iff base m t ht u V V hV
    (fun _ => Set.Subset.rfl) hu).mp hNm
  have hboundedR := (paperAtlasWeighted_ne_top_iff base r t ht u V V hV
    (fun _ => Set.Subset.rfl) hu).mp hNr
  have hfinM : ∀ a ≤ m, paperAtlasCj (a + base) u V V ≠ ⊤ := by
    intro a ha
    apply (paperAtlasCj_ne_top_iff (a + base) u V V hV (fun _ => Set.Subset.rfl) hu).mpr
    intro i k hk
    exact hboundedM i k (by omega)
  have hfinR : paperAtlasCj (r + base) u V V ≠ ⊤ := by
    apply (paperAtlasCj_ne_top_iff (r + base) u V V hV (fun _ => Set.Subset.rfl) hu).mpr
    exact hboundedR
  have hhighRaw (a : ℕ) (ha : a ≤ m) := paperAtlasCj_smoothing_error_high_le mu
    (finiteMomentKernel_contDiff hsmooth r) (finiteMomentKernel_hasCompactSupport hcompact r)
    u U V hU hV hUV hu ell hbuffer (a + base) (hfinM a ha)
  have houtC : paperAtlasCj (m + base) e U U ≠ ⊤ := (hhighRaw m le_rfl).1
  have houtBounded := (paperAtlasCj_ne_top_iff (m + base) e U U hU
    (fun _ => Set.Subset.rfl) he).mp houtC
  have hout : paperAtlasWeighted base m tau e U U ≠ ⊤ :=
    paperAtlasWeighted_ne_top base m tau e U U hU (fun _ => Set.Subset.rfl) he houtBounded
  have hlow : ∀ a ≤ m, a ≤ r → A a ≤ L * ell ^ (r - a) * I r := by
    intro a _ har
    exact (paperAtlasCj_smoothing_error_shifted_low_le mu hsmooth hcompact hmass base r a har
      u U V hU hV hUV hu hell.le hsegments hfinR).2
  have hhigh : ∀ a ≤ m, A a ≤ H * I a := by
    intro a ha
    exact (hhighRaw a ha).2.trans (mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left
        (coordinateDimensionFactor_mono d (Nat.add_le_add_right ha base)) hmassabs)
      ENNReal.toReal_nonneg)
  have hNrSum : (∑ a ∈ Finset.range (r + 1), t ^ a * I a) ≤ B := by
    rw [paperAtlasWeighted_toReal base r t ht.le u V V hNr] at hB
    exact hB
  have hw := weighted_low_high_tail m r I A (fun _ => ENNReal.toReal_nonneg)
    L H hL hH htau.le htaul helt ht B hNrSum hlow hhigh
  refine ⟨hout, ?_⟩
  rw [paperAtlasWeighted_toReal base m tau htau.le _ U U hout,
    paperAtlasWeighted_toReal base m t ht.le u V V hNm]
  exact hw

/-- The combined map/tensor form of (6.4), with the map's true base-two
shift and the tensor's base-zero norm, when all displayed domain
coordinates are spatial. Both errors use the same actual signed
moment kernel and the same scale. This theorem makes no identification
of a parameter-product total C2 norm with a spatial-only two-jet norm. -/
theorem paperAtlasWeighted_map_tensor_smoothing_tail {ι : Type*} [Fintype ι] {qG qH : ℕ}
    {kappa : (Fin d → ℝ) → ℝ} (hsmooth : ContDiff ℝ ∞ kappa)
    (hcompact : HasCompactSupport kappa) (hmass : (∫ y, kappa y ∂mu) = 1)
    (m r : ℕ) (G : ι → (Fin d → ℝ) → Fin qG → ℝ) (H : ι → (Fin d → ℝ) → Fin qH → ℝ)
    (U V : ι → Set (Fin d → ℝ))
    (hU : ∀ i, IsOpen (U i)) (hV : ∀ i, IsOpen (V i)) (hUV : ∀ i, U i ⊆ V i)
    (hG : ∀ i, ContDiffOn ℝ ∞ (G i) (V i)) (hH : ∀ i, ContDiffOn ℝ ∞ (H i) (V i))
    {tau ell t : ℝ} (htau : 0 < tau) (htaul : tau ≤ ell) (helt : ell ≤ t)
    (hsegments : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ s ∈ Set.Icc (0 : ℝ) 1, x - s • (ell • y) ∈ V i)
    (hGr : paperAtlasWeighted 2 r t G V V ≠ ⊤) (hGm : paperAtlasWeighted 2 m t G V V ≠ ⊤)
    (hHr : paperAtlasWeighted 0 r t H V V ≠ ⊤) (hHm : paperAtlasWeighted 0 m t H V V ≠ ⊤)
    (B : ℝ) (hB : (paperAtlasWeighted 2 r t G V V).toReal +
      (paperAtlasWeighted 0 r t H V V).toReal ≤ B) :
    let K := finiteMomentKernel r kappa
    let eG := fun i x => G i x - signedSmoothing mu K ell (G i) x
    let eH := fun i x => H i x - signedSmoothing mu K ell (H i) x
    paperAtlasWeighted 2 m tau eG U U ≠ ⊤ ∧ paperAtlasWeighted 0 m tau eH U U ≠ ⊤ ∧
      (paperAtlasWeighted 2 m tau eG U U).toReal + (paperAtlasWeighted 0 m tau eH U U).toReal ≤
        (paperShiftedSmoothingTailConstant mu kappa 2 m r +
          paperShiftedSmoothingTailConstant mu kappa 0 m r) *
          (B * (ell / t) ^ r +
            ((paperAtlasWeighted 2 m t G V V).toReal +
              (paperAtlasWeighted 0 m t H V V).toReal) * (tau / t) ^ r) := by
  dsimp only
  have hbuffer : ∀ i, ∀ x ∈ U i, ∀ y ∈ tsupport (finiteMomentKernel r kappa), x - ell • y ∈ V i := by
    intro i x hx y hy
    simpa only [one_smul] using hsegments i x hx y hy 1 (by simp)
  have hSG : ∀ i, ContDiffOn ℝ ∞
      (signedSmoothing mu (finiteMomentKernel r kappa) ell (G i)) (U i) := fun i =>
    signedSmoothing_contDiffOn mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) (hU i) (hV i) (hG i) ell (hbuffer i)
  have hSH : ∀ i, ContDiffOn ℝ ∞
      (signedSmoothing mu (finiteMomentKernel r kappa) ell (H i)) (U i) := fun i =>
    signedSmoothing_contDiffOn mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) (hU i) (hV i) (hH i) ell (hbuffer i)
  rw [paperAtlasWeighted_sub_comm 2 m tau G
      (fun i => signedSmoothing mu (finiteMomentKernel r kappa) ell (G i)) U U hU
      (fun _ => Set.Subset.rfl) (fun i => (hG i).mono (hUV i)) hSG,
    paperAtlasWeighted_sub_comm 0 m tau H
      (fun i => signedSmoothing mu (finiteMomentKernel r kappa) ell (H i)) U U hU
      (fun _ => Set.Subset.rfl) (fun i => (hH i).mono (hUV i)) hSH]
  have hBG : (paperAtlasWeighted 2 r t G V V).toReal ≤ B :=
    (le_add_of_nonneg_right ENNReal.toReal_nonneg).trans hB
  have hBH : (paperAtlasWeighted 0 r t H V V).toReal ≤ B :=
    (le_add_of_nonneg_left ENNReal.toReal_nonneg).trans hB
  have hg := paperAtlasWeighted_smoothing_tail_totalShift mu hsmooth hcompact hmass 2 m r G U V
    hU hV hUV hG htau htaul helt hsegments hGr hGm B hBG
  have hh := paperAtlasWeighted_smoothing_tail_totalShift mu hsmooth hcompact hmass 0 m r H U V
    hU hV hUV hH htau htaul helt hsegments hHr hHm B hBH
  refine ⟨hg.1, hh.1, (add_le_add hg.2 hh.2).trans ?_⟩
  have ht : 0 < t := htau.trans_le (htaul.trans helt)
  have hratio : 0 ≤ (tau / t) ^ r := pow_nonneg (div_nonneg htau.le ht.le) _
  calc
    _ ≤ paperShiftedSmoothingTailConstant mu kappa 2 m r *
          (B * (ell / t) ^ r +
            ((paperAtlasWeighted 2 m t G V V).toReal +
              (paperAtlasWeighted 0 m t H V V).toReal) * (tau / t) ^ r) +
        paperShiftedSmoothingTailConstant mu kappa 0 m r *
          (B * (ell / t) ^ r +
            ((paperAtlasWeighted 2 m t G V V).toReal +
              (paperAtlasWeighted 0 m t H V V).toReal) * (tau / t) ^ r) := by
      apply add_le_add
      · apply mul_le_mul_of_nonneg_left _ (paperShiftedSmoothingTailConstant_nonneg mu kappa 2 m r)
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right ENNReal.toReal_nonneg) hratio)
      · apply mul_le_mul_of_nonneg_left _ (paperShiftedSmoothingTailConstant_nonneg mu kappa 0 m r)
        exact add_le_add le_rfl
          (mul_le_mul_of_nonneg_right (le_add_of_nonneg_left ENNReal.toReal_nonneg) hratio)
    _ = _ := by ring

end

end GlobalEmbedding.Offline
