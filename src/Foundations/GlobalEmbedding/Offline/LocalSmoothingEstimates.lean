import GlobalEmbedding.Offline.LocalSmoothingDerivatives
import GlobalEmbedding.Offline.IteratedJetNorms

/-!
# Quantitative genuine jets of local smoothing errors

Source: `literature/parallelizable-stable-plus-one/main.tex`, lines 700–719,
and `repair-local-convolution-estimates`. Taylor cancellation is applied
to the actual source jets, whose smoothing is proved to be the actual
jet of the same convolution. Local segment assumptions express exactly
the buffer needed by the remainder estimate. The high-order estimate
uses the true absolute L1 mass of the signed kernel.
-/

open MeasureTheory
open scoped ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] [CompleteSpace F]
    [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [mu.IsAddHaarMeasure]

/-- A fixed real tail constant containing the signed kernel's absolute
mass and every absolute moment used by Taylor through order r. -/
def kernelTailConstant (K : E → ℝ) (r : ℕ) : ℝ :=
  1 + (∫ y, |K y| ∂mu) + ∑ n ∈ Finset.range r,
    (∫ y, |K y| * ‖y‖ ^ (n + 1) ∂mu) / (n.factorial : ℝ)

omit [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The direct signed L1 error constant is one of the contributions to
the fixed tail constant. -/
theorem one_add_L1_le_kernelTailConstant (K : E → ℝ) (r : ℕ) :
    1 + (∫ y, |K y| ∂mu) ≤ kernelTailConstant mu K r := by
  unfold kernelTailConstant
  apply le_add_of_nonneg_right
  exact Finset.sum_nonneg fun n _ => div_nonneg
    (integral_nonneg fun y => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) _))
    (Nat.cast_nonneg _)

omit [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- Each factorial-normalized absolute Taylor moment is controlled by
the same finite fixed-template constant. -/
theorem moment_le_kernelTailConstant (K : E → ℝ) {r n : ℕ} (hn : n < r) :
    (∫ y, |K y| * ‖y‖ ^ (n + 1) ∂mu) / (n.factorial : ℝ) ≤
      kernelTailConstant mu K r := by
  have hnonneg : ∀ k : ℕ,
      0 ≤ (∫ y, |K y| * ‖y‖ ^ (k + 1) ∂mu) / (k.factorial : ℝ) := by
    intro k
    exact div_nonneg
      (integral_nonneg fun y => mul_nonneg (abs_nonneg _) (pow_nonneg (norm_nonneg _) _))
      (Nat.cast_nonneg _)
  exact (Finset.single_le_sum (fun k _ => hnonneg k) (Finset.mem_range.mpr hn)).trans
    (le_add_of_nonneg_left (add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg _)))

omit [NormedSpace ℝ E] [BorelSpace E] [FiniteDimensional ℝ E] [mu.IsAddHaarMeasure] in
/-- The fixed tail constant is nonnegative, including order zero and
zero-dimensional domains. -/
theorem kernelTailConstant_nonneg (K : E → ℝ) (r : ℕ) :
    0 ≤ kernelTailConstant mu K r :=
  (add_nonneg zero_le_one (integral_nonneg fun y => abs_nonneg (K y))).trans
    (one_add_L1_le_kernelTailConstant mu K r)

/-- The native derivative of the actual error is the error in smoothing
the native source derivative, on the same output domain. -/
theorem signedSmoothing_iteratedFDeriv_error {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ x ∈ U, ∀ y ∈ tsupport K, x - ell • y ∈ V)
    (j : ℕ) {x : E} (hx : x ∈ U) :
    iteratedFDeriv ℝ j (fun z => signedSmoothing mu K ell u z - u z) x =
      signedSmoothing mu K ell (iteratedFDeriv ℝ j u) x - iteratedFDeriv ℝ j u x := by
  have hs := signedSmoothing_contDiffOn mu hK hKcompact hU hV hu ell hbuffer
  change iteratedFDeriv ℝ j (signedSmoothing mu K ell u - u) x = _
  rw [iteratedFDeriv_sub_apply
    ((hs.contDiffAt (hU.mem_nhds hx)).of_le (by simp))
    ((hu.contDiffAt (hV.mem_nhds (hUV hx))).of_le (by simp))]
  rw [signedSmoothing_iteratedFDeriv_source_on mu hK hKcompact hU hV hu ell hbuffer j hx]
  rfl

/-- Low-order Taylor tail for the actual j-th derivative of the actual
convolution error. Degree-n moment cancellation needs an order
n+1+j source bound. The constant is the true absolute kernel moment. -/
theorem signedSmoothing_derivative_error_le {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1)
    (r n j : ℕ) (hnr : n ≤ r)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hsegments : ∀ z ∈ U, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, z - t • (ell • y) ∈ V)
    {x : E} (hx : x ∈ U) (B : ℝ)
    (hB : ∀ y ∈ Function.support (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1,
        ‖iteratedFDeriv ℝ (n + 1 + j) u (x - t • (ell • y))‖ ≤ B) :
    ‖iteratedFDeriv ℝ j
        (fun z => signedSmoothing mu (finiteMomentKernel r kappa) ell u z - u z) x‖ ≤
      (B * |ell| ^ (n + 1) / (n.factorial : ℝ)) *
        ∫ y, |finiteMomentKernel r kappa y| * ‖y‖ ^ (n + 1) ∂mu := by
  have hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport (finiteMomentKernel r kappa), z - ell • y ∈ V := by
    intro z hz y hy
    simpa only [one_smul] using hsegments z hz y hy 1 (by simp)
  rw [signedSmoothing_iteratedFDeriv_error mu (finiteMomentKernel_contDiff hsmooth r)
    (finiteMomentKernel_hasCompactSupport hcompact r) hU hV hUV hu ell hbuffer j hx]
  apply signedSmoothing_error_le_of_contDiffAt mu hsmooth hcompact hmass r n hnr x ell B
  · intro y hy t ht
    exact (hu.contDiffAt (hV.mem_nhds (hsegments x hx y hy t ht))).iteratedFDeriv_right (by simp)
  · intro y hy t ht
    rw [norm_iteratedFDeriv_iteratedFDeriv]
    exact hB y hy t ht

/-- At arbitrary derivative order, the signed-kernel L1 bound controls
the actual error using only a bound on the same source derivative.
This includes the borderline Taylor order and the high-order tail. -/
theorem signedSmoothing_derivative_error_le_L1 {K : E → ℝ}
    (hK : ContDiff ℝ ∞ K) (hKcompact : HasCompactSupport K)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hu : ContDiffOn ℝ ∞ u V) (ell : ℝ)
    (hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V)
    (j : ℕ) {x : E} (hx : x ∈ U) (B : ℝ)
    (hB : ∀ z ∈ V, ‖iteratedFDeriv ℝ j u z‖ ≤ B) :
    ‖iteratedFDeriv ℝ j (fun z => signedSmoothing mu K ell u z - u z) x‖ ≤
      (1 + ∫ y, |K y| ∂mu) * B := by
  rw [signedSmoothing_iteratedFDeriv_error mu hK hKcompact hU hV hUV hu ell hbuffer j hx]
  have hInt : Integrable (fun y => |K y| * B) mu :=
    (hK.continuous.integrable_of_hasCompactSupport hKcompact).norm.mul_const B
  have hS : ‖signedSmoothing mu K ell (iteratedFDeriv ℝ j u) x‖ ≤
      (∫ y, |K y| ∂mu) * B := by
    change ‖∫ y, K y • iteratedFDeriv ℝ j u (x - ell • y) ∂mu‖ ≤ _
    rw [← integral_mul_const]
    apply norm_integral_le_of_norm_le hInt
    filter_upwards [] with y
    by_cases hy : K y = 0
    · simp only [hy, zero_smul, norm_zero, abs_zero, zero_mul, le_refl]
    · rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left
        (hB _ (hbuffer x hx y (subset_tsupport K hy))) (abs_nonneg _)
  calc
    ‖signedSmoothing mu K ell (iteratedFDeriv ℝ j u) x - iteratedFDeriv ℝ j u x‖ ≤
        ‖signedSmoothing mu K ell (iteratedFDeriv ℝ j u) x‖ + ‖iteratedFDeriv ℝ j u x‖ :=
      norm_sub_le _ _
    _ ≤ (∫ y, |K y| ∂mu) * B + B := add_le_add hS (hB x (hUV hx))
    _ = (1 + ∫ y, |K y| ∂mu) * B := by ring

/-- Uniform low-order estimate with the same fixed template constant,
including the borderline derivative order j=r. All source derivatives
through r are genuinely bounded on the local buffer. -/
theorem signedSmoothing_low_derivative_error_le {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1) (r : ℕ)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 ≤ ell)
    (hsegments : ∀ z ∈ U, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, z - t • (ell • y) ∈ V)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ k ≤ r, ∀ z ∈ V, ‖iteratedFDeriv ℝ k u z‖ ≤ B)
    {j : ℕ} (hjr : j ≤ r) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ j
        (fun z => signedSmoothing mu (finiteMomentKernel r kappa) ell u z - u z) x‖ ≤
      kernelTailConstant mu (finiteMomentKernel r kappa) r * B * ell ^ (r - j) := by
  let K := finiteMomentKernel r kappa
  have hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V := by
    intro z hz y hy
    simpa only [one_smul] using hsegments z hz y hy 1 (by simp)
  rcases eq_or_lt_of_le hjr with hjeq | hjlt
  · subst j
    have h := signedSmoothing_derivative_error_le_L1 mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) hU hV hUV hu ell hbuffer r hx B (hB r le_rfl)
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact h.trans (mul_le_mul_of_nonneg_right (one_add_L1_le_kernelTailConstant mu K r) hB0)
  · let n := r - j - 1
    have hn : n < r := by dsimp [n]; omega
    have horder : n + 1 + j = r := by dsimp [n]; omega
    have hpower : n + 1 = r - j := by omega
    have h := signedSmoothing_derivative_error_le mu hsmooth hcompact hmass r n j hn.le
      hU hV hUV hu ell hsegments hx B (by
        intro y hy t ht
        rw [horder]
        exact hB r le_rfl _ (hsegments x hx y (subset_tsupport K hy) t ht))
    rw [abs_of_nonneg hell] at h
    calc
      _ ≤ (B * ell ^ (n + 1) / (n.factorial : ℝ)) *
          ∫ y, |K y| * ‖y‖ ^ (n + 1) ∂mu := h
      _ = ((∫ y, |K y| * ‖y‖ ^ (n + 1) ∂mu) / (n.factorial : ℝ)) *
          (B * ell ^ (n + 1)) := by ring
      _ ≤ kernelTailConstant mu K r * (B * ell ^ (n + 1)) :=
        mul_le_mul_of_nonneg_right (moment_le_kernelTailConstant mu K hn)
          (mul_nonneg hB0 (pow_nonneg hell _))
      _ = _ := by rw [hpower, mul_assoc]

/-- A fixed total derivative shift can be retained in the cumulative
low-order estimate. For all k≤j+base, Taylor is taken to the common
degree r-j-1, so only derivatives through r+base are used. At j=r the
direct signed L1 bound applies. This statement concerns total
derivatives; it makes no identification with spatial-only derivatives
on a parameter product. -/
theorem signedSmoothing_low_shifted_derivative_error_le {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ y, kappa y ∂mu) = 1) (base r j : ℕ) (hjr : j ≤ r)
    {u : E → F} {U V : Set E} (hU : IsOpen U) (hV : IsOpen V) (hUV : U ⊆ V)
    (hu : ContDiffOn ℝ ∞ u V) {ell : ℝ} (hell : 0 ≤ ell)
    (hsegments : ∀ z ∈ U, ∀ y ∈ tsupport (finiteMomentKernel r kappa),
      ∀ t ∈ Set.Icc (0 : ℝ) 1, z - t • (ell • y) ∈ V)
    (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ a ≤ r + base, ∀ z ∈ V, ‖iteratedFDeriv ℝ a u z‖ ≤ B)
    {k : ℕ} (hk : k ≤ j + base) {x : E} (hx : x ∈ U) :
    ‖iteratedFDeriv ℝ k
        (fun z => signedSmoothing mu (finiteMomentKernel r kappa) ell u z - u z) x‖ ≤
      kernelTailConstant mu (finiteMomentKernel r kappa) r * B * ell ^ (r - j) := by
  let K := finiteMomentKernel r kappa
  rcases eq_or_lt_of_le hjr with hjeq | hjlt
  · subst j
    have hbuffer : ∀ z ∈ U, ∀ y ∈ tsupport K, z - ell • y ∈ V := by
      intro z hz y hy
      simpa only [one_smul] using hsegments z hz y hy 1 (by simp)
    have h := signedSmoothing_derivative_error_le_L1 mu (finiteMomentKernel_contDiff hsmooth r)
      (finiteMomentKernel_hasCompactSupport hcompact r) hU hV hUV hu ell hbuffer k hx B (hB k hk)
    simp only [Nat.sub_self, pow_zero, mul_one]
    exact h.trans (mul_le_mul_of_nonneg_right (one_add_L1_le_kernelTailConstant mu K r) hB0)
  · let n := r - j - 1
    have hn : n < r := by dsimp [n]; omega
    have horder : n + 1 + k ≤ r + base := by dsimp [n]; omega
    have hpower : n + 1 = r - j := by dsimp [n]; omega
    have h := signedSmoothing_derivative_error_le mu hsmooth hcompact hmass r n k hn.le
      hU hV hUV hu ell hsegments hx B (by
        intro y hy t ht
        exact hB (n + 1 + k) horder _ (hsegments x hx y (subset_tsupport K hy) t ht))
    rw [abs_of_nonneg hell] at h
    calc
      _ ≤ (B * ell ^ (n + 1) / (n.factorial : ℝ)) *
          ∫ y, |K y| * ‖y‖ ^ (n + 1) ∂mu := h
      _ = ((∫ y, |K y| * ‖y‖ ^ (n + 1) ∂mu) / (n.factorial : ℝ)) *
          (B * ell ^ (n + 1)) := by ring
      _ ≤ kernelTailConstant mu K r * (B * ell ^ (n + 1)) :=
        mul_le_mul_of_nonneg_right (moment_le_kernelTailConstant mu K hn)
          (mul_nonneg hB0 (pow_nonneg hell _))
      _ = _ := by rw [hpower, mul_assoc]

end

end GlobalEmbedding.Offline
