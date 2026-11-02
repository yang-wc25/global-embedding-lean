import GlobalEmbedding.Offline.MomentKernelExistence
import GlobalEmbedding.Offline.TaylorAlongLine
import Mathlib.Analysis.LocallyConvex.SeparatingDual

/-!
# Signed finite-moment smoothing and exact Taylor cancellation

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
and `dag/nodes/repair-local-convolution-estimates.json`.

The integral below uses the actual signed kernel and a genuine source
function. Compact support is required for the kernel only. The source is
allowed to have noncompact support. The moment construction annihilates
the native Fréchet Taylor terms by multilinear homogeneity, so no new
Vandermonde or formal placeholder for polynomial cancellation is used.
-/

open MeasureTheory
open scoped BigOperators ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]

/-- The actual scale-`ell` smoothing integral, written with the fixed
template kernel after the usual change of variables. -/
def signedSmoothing (K : E → ℝ) (ell : ℝ) (u : E → F) (x : E) : F :=
  ∫ y, K y • u (x - ell • y) ∂mu

/-- Continuous vector-valued homogeneous functions have zero moment
against the actual finite-moment kernel. Apply each continuous linear
functional to the integral and reuse the scalar moment theorem. -/
theorem finiteMomentKernel_vector_moment {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (r : ℕ) (P : E → F) (hPcont : Continuous P) {k : ℕ}
    (hk0 : 0 < k) (hkr : k ≤ r)
    (hP : ∀ (a : ℝ) (x : E), P (a • x) = a ^ k • P x) :
    (∫ x, finiteMomentKernel r kappa x • P x ∂mu) = 0 := by
  have hInt : Integrable (fun x => finiteMomentKernel r kappa x • P x) mu :=
    ((finiteMomentKernel_contDiff hsmooth r).continuous.smul hPcont).integrable_of_hasCompactSupport
      (finiteMomentKernel_hasCompactSupport hcompact r).smul_right
  apply SeparatingDual.eq_zero_of_forall_dual_eq_zero (R := ℝ)
  intro L
  rw [← L.integral_comp_comm hInt]
  simp only [map_smul, smul_eq_mul]
  have hscalar := finiteMomentKernel_homogeneous_moment mu hsmooth hcompact r
    (fun x => L (P x)) (L.continuous.comp hPcont) hk0 hkr (by
      intro a x
      simp only [hP, map_smul, smul_eq_mul])
  simpa only [mul_comm] using hscalar

omit [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Diagonal evaluation of a fixed continuous multilinear map is
continuous as a function of the increment. -/
theorem multilinearDiagonal_continuous (k : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) (c : ℝ) :
    Continuous (fun y : E => A (fun _ => c • y)) :=
  A.cont.comp (continuous_pi fun _ => continuous_const.smul continuous_id)

omit [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- Multilinearity gives the exact degree of each diagonal Taylor term. -/
theorem multilinearDiagonal_smul (k : ℕ)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F)
    (c a : ℝ) (y : E) :
    A (fun _ => c • (a • y)) = a ^ k • A (fun _ => c • y) := by
  simp_rw [smul_comm c a y]
  simpa using A.map_smul_univ (fun _ => a) (fun _ => c • y)

omit [CompleteSpace F] [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E] in
/-- The actual finite Fréchet Taylor polynomial is continuous in its
increment, even when no differentiability is assumed of the source. -/
theorem frechetTaylor_continuous_increment (u : E → F) (n : ℕ) (x : E) (c : ℝ) :
    Continuous (fun y : E => frechetTaylor u n x (c • y)) := by
  exact continuous_finsetSum _ fun k _ =>
    continuous_const.smul (multilinearDiagonal_continuous k _ c)

/-- Every positive-degree diagonal Fréchet Taylor term through the chosen
moment order has zero integral against the constructed kernel. -/
theorem finiteMomentKernel_diagonal_moment {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (r k : ℕ) (hk0 : 0 < k) (hkr : k ≤ r)
    (A : ContinuousMultilinearMap ℝ (fun _ : Fin k => E) F) (c : ℝ) :
    (∫ y, finiteMomentKernel r kappa y • A (fun _ => c • y) ∂mu) = 0 :=
  finiteMomentKernel_vector_moment mu hsmooth hcompact r
    (fun y => A (fun _ => c • y)) (multilinearDiagonal_continuous k A c)
    hk0 hkr (multilinearDiagonal_smul k A c)

/-- Integrating the actual Fréchet Taylor polynomial against the signed
finite-moment kernel preserves exactly its constant term.

Proof: finite-sum linearity is justified by continuity and compact kernel
support. Each positive-degree term has zero integral by the preceding
multilinear moment theorem, while the degree-zero term is the actual
value `u x` and uses the actual mass-one identity. -/
theorem finiteMomentKernel_frechetTaylor_integral {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1)
    (r n : ℕ) (hnr : n ≤ r) (u : E → F) (x : E) (c : ℝ) :
    (∫ y, finiteMomentKernel r kappa y • frechetTaylor u n x (c • y) ∂mu) = u x := by
  let K := finiteMomentKernel r kappa
  have hKcont := (finiteMomentKernel_contDiff hsmooth r).continuous
  have hKcompact := finiteMomentKernel_hasCompactSupport hcompact r
  have hInt : ∀ k : ℕ, Integrable
      (fun y => K y • ((k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k u x (fun _ => c • y))) mu := by
    intro k
    have hcont : Continuous (fun y : E => (k.factorial : ℝ)⁻¹ •
        iteratedFDeriv ℝ k u x (fun _ => c • y)) :=
      continuous_const.smul (multilinearDiagonal_continuous k _ c)
    exact (hKcont.smul hcont).integrable_of_hasCompactSupport hKcompact.smul_right
  simp_rw [frechetTaylor, Finset.smul_sum]
  rw [integral_finsetSum _ (fun k _ => hInt k)]
  rw [Finset.sum_eq_single 0]
  · simp only [Nat.factorial_zero, Nat.cast_one, inv_one, one_smul,
      iteratedFDeriv_zero_apply]
    rw [integral_smul_const, finiteMomentKernel_integral mu hsmooth hcompact hmass r, one_smul]
  · intro k hk hk0
    have hkr : k ≤ r := (Nat.le_of_lt_succ (Finset.mem_range.mp hk)).trans hnr
    have hm := finiteMomentKernel_diagonal_moment mu hsmooth hcompact r k
      (Nat.pos_of_ne_zero hk0) hkr (iteratedFDeriv ℝ k u x) c
    calc
      (∫ y, K y • ((k.factorial : ℝ)⁻¹ •
          iteratedFDeriv ℝ k u x (fun _ => c • y)) ∂mu) =
          ∫ y, (k.factorial : ℝ)⁻¹ •
            (K y • iteratedFDeriv ℝ k u x (fun _ => c • y)) ∂mu := by
        apply integral_congr_ae
        filter_upwards [] with y
        exact smul_comm _ _ _
      _ = (k.factorial : ℝ)⁻¹ • ∫ y,
          K y • iteratedFDeriv ℝ k u x (fun _ => c • y) ∂mu := integral_smul _ _
      _ = 0 := by rw [hm, smul_zero]
  · simp

/-- Quantitative local approximation by the actual signed finite-moment
convolution, of every finite order supported by the template moments.

Regularity and the derivative bound are required only on actual segments
joining `x` to `x - ell • y` for `y` in the kernel's topological support.
No global regularity or compact support of `u` and no pre-existing
remainder bound are assumed. The constant is the true absolute moment
of the constructed signed kernel. The exponent is
`n + 1`, with Taylor polynomial degree `n`; for `r ≥ 1`, taking
`n = r - 1` gives the paper's `C^r` low-order tail.
-/
theorem signedSmoothing_error_le_of_contDiffAt {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1)
    (r n : ℕ) (hnr : n ≤ r) {u : E → F}
    (x : E) (ell B : ℝ)
    (hu : ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ContDiffAt ℝ (n + 1) u (x - t • (ell • y)))
    (hB : ∀ y ∈ Function.support (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1) u (x - t • (ell • y))‖ ≤ B) :
    ‖signedSmoothing mu (finiteMomentKernel r kappa) ell u x - u x‖ ≤
      (B * |ell| ^ (n + 1) / (n.factorial : ℝ)) *
        ∫ y, |finiteMomentKernel r kappa y| * ‖y‖ ^ (n + 1) ∂mu := by
  let K := finiteMomentKernel r kappa
  let T := fun y : E => frechetTaylor u n x ((-ell) • y)
  have hKcont : Continuous K := (finiteMomentKernel_contDiff hsmooth r).continuous
  have hKcompact : HasCompactSupport K := finiteMomentKernel_hasCompactSupport hcompact r
  have hUcont : ContinuousOn (fun y : E => u (x - ell • y)) (tsupport K) := by
    intro y hy
    have h := (hu y hy 1 (by simp)).continuousAt
    simp only [one_smul] at h
    have hmap : Continuous (fun z : E => x - ell • z) :=
      continuous_const.sub (continuous_const.smul continuous_id)
    exact (h.comp (x := y) hmap.continuousAt).continuousWithinAt
  have hTcont : Continuous T := frechetTaylor_continuous_increment u n x (-ell)
  have hUI : Integrable (fun y => K y • u (x - ell • y)) mu :=
    (integrableOn_iff_integrable_of_support_subset
      ((Function.support_smul_subset_left _ _).trans (subset_tsupport K))).mp
      ((hKcont.continuousOn.smul hUcont).integrableOn_compact hKcompact)
  have hTI : Integrable (fun y => K y • T y) mu :=
    (hKcont.smul hTcont).integrable_of_hasCompactSupport hKcompact.smul_right
  have hcancel : (∫ y, K y • T y ∂mu) = u x :=
    finiteMomentKernel_frechetTaylor_integral mu hsmooth hcompact hmass r n hnr u x (-ell)
  have herror : signedSmoothing mu K ell u x - u x =
      ∫ y, K y • (u (x - ell • y) - T y) ∂mu := by
    rw [signedSmoothing, ← hcancel, ← integral_sub hUI hTI]
    apply integral_congr_ae
    filter_upwards [] with y
    exact (smul_sub _ _ _).symm
  have hmoment : Integrable (fun y => |K y| * ‖y‖ ^ (n + 1)) mu :=
    (hKcont.abs.mul (continuous_norm.pow _)).integrable_of_hasCompactSupport hKcompact.abs.mul_right
  have hpoint : ∀ y : E,
      ‖K y • (u (x - ell • y) - T y)‖ ≤
        (B * |ell| ^ (n + 1) / (n.factorial : ℝ)) * (|K y| * ‖y‖ ^ (n + 1)) := by
    intro y
    by_cases hy : K y = 0
    · simp [hy]
    have hTaylor := norm_sub_frechetTaylor_le_of_contDiffAt x ((-ell) • y) B
      (by
        intro t ht
        simpa only [neg_smul, smul_neg, ← sub_eq_add_neg] using
          hu y (subset_tsupport K hy) t ht)
      (by
        intro t ht
        simpa only [neg_smul, smul_neg, ← sub_eq_add_neg] using hB y hy t ht)
    have hTaylor' : ‖u (x - ell • y) - T y‖ ≤
        B * (|ell| * ‖y‖) ^ (n + 1) / (n.factorial : ℝ) := by
      simpa only [T, neg_smul, ← sub_eq_add_neg, norm_neg, norm_smul,
        Real.norm_eq_abs] using hTaylor
    rw [norm_smul, Real.norm_eq_abs]
    calc
      |K y| * ‖u (x - ell • y) - T y‖ ≤
          |K y| * (B * (|ell| * ‖y‖) ^ (n + 1) / (n.factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left hTaylor' (abs_nonneg _)
      _ = (B * |ell| ^ (n + 1) / (n.factorial : ℝ)) * (|K y| * ‖y‖ ^ (n + 1)) := by
        rw [mul_pow]
        ring
  rw [herror]
  calc
    ‖∫ y, K y • (u (x - ell • y) - T y) ∂mu‖ ≤
        ∫ y, (B * |ell| ^ (n + 1) / (n.factorial : ℝ)) * (|K y| * ‖y‖ ^ (n + 1)) ∂mu :=
      norm_integral_le_of_norm_le (hmoment.const_mul _) (Filter.Eventually.of_forall hpoint)
    _ = _ := integral_const_mul _ _

/-- The global-regularity specialization of the local approximation
estimate. The quantitative derivative bound is still only required
along the actual kernel segments, and the source need not be compactly
supported. -/
theorem signedSmoothing_error_le {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1)
    (r n : ℕ) (hnr : n ≤ r) {u : E → F} (hu : ContDiff ℝ (n + 1) u)
    (x : E) (ell B : ℝ)
    (hB : ∀ y ∈ Function.support (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1) u (x - t • (ell • y))‖ ≤ B) :
    ‖signedSmoothing mu (finiteMomentKernel r kappa) ell u x - u x‖ ≤
      (B * |ell| ^ (n + 1) / (n.factorial : ℝ)) *
        ∫ y, |finiteMomentKernel r kappa y| * ‖y‖ ^ (n + 1) ∂mu :=
  signedSmoothing_error_le_of_contDiffAt mu hsmooth hcompact hmass r n hnr x ell B
    (fun _ _ _ _ => hu.contDiffAt) hB

end

end GlobalEmbedding.Offline
