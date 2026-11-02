import Smoothing.TensorLocalNormalization

/-!
# Uniform jets for the actual parameter-local normalization

The fixed denominator repair from TensorLocalNormalization is differentiated
at every order. Its bound is constructed from the ORIGINAL active raw-cutoff
derivative profile and overlap multiplicity. No normalized cutoff or output
bound is assumed, and no total index count enters any constant.
-/

open Function Set Filter
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Offline

noncomputable section
set_option backward.isDefEq.respectTransparency false

def tensorCoverageDenominator (s : ℝ) : ℝ := tensorCoverageBump s ^ 2 + s

theorem tensorCoverageDenominator_contDiff : ContDiff ℝ ∞ tensorCoverageDenominator :=
  tensorCoverageBump.contDiff.pow 2 |>.add contDiff_id

/-- All derivatives of the same fixed scalar denominator on a fixed compact
interval have one cumulative bound. This is an existence proof from native
continuity and compactness, not a derivative-provider hypothesis. -/
theorem exists_tensorCoverageDenominator_derivative_bounds (C0 : ℝ) :
    ∃ R : ℕ → ℝ, (∀ j, 0 ≤ R j) ∧ ∀ j k, k ≤ j →
      ∀ s ∈ Icc (0 : ℝ) (max 0 C0),
      ‖iteratedFDeriv ℝ k tensorCoverageDenominator s‖ ≤ R j := by
  have hbound (k : ℕ) : ∃ a : ℝ, 0 ≤ a ∧ ∀ s ∈ Icc (0 : ℝ) (max 0 C0),
      ‖iteratedFDeriv ℝ k tensorCoverageDenominator s‖ ≤ a := by
    have hc : Continuous (fun s => ‖iteratedFDeriv ℝ k tensorCoverageDenominator s‖) :=
      (tensorCoverageDenominator_contDiff.continuous_iteratedFDeriv (by simp)).norm
    obtain ⟨a, ha⟩ := (isCompact_Icc : IsCompact (Icc (0 : ℝ) (max 0 C0))).bddAbove_image hc.continuousOn
    exact ⟨max 0 a, le_max_left _ _, fun s hs => (ha ⟨s, hs, rfl⟩).trans (le_max_right _ _)⟩
  choose a ha hbound using hbound
  refine ⟨fun j => ∑ k ∈ Finset.range (j + 1), a k,
    fun j => Finset.sum_nonneg (fun k _ => ha k), ?_⟩
  intro j k hkj s hs
  exact (hbound k s hs).trans (Finset.single_le_sum (fun i _ => ha i) (by simpa using hkj))

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- A genuine bounded nonnegative scalar source produces all true
denominator jets, uniformly before the source and its domain are chosen. -/
theorem exists_tensorCoverageDenominator_composition_bounds
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j) :
    ∃ D : ℕ → ℝ, (∀ j, 0 ≤ D j) ∧
      ∀ (S : E → ℝ) (O : Set E), IsOpen O → ContDiffOn ℝ ∞ S O →
      (∀ x ∈ O, 0 ≤ S x) →
      (∀ j, ∀ x ∈ O, ‖iteratedFDeriv ℝ j S x‖ ≤ C j) →
      ∀ j, ∀ x ∈ O, ‖iteratedFDeriv ℝ j (tensorCoverageDenominator ∘ S) x‖ ≤ D j := by
  obtain ⟨R, hR, hscalar⟩ := exists_tensorCoverageDenominator_derivative_bounds (C 0)
  refine ⟨fun j => (j.factorial : ℝ) * R j * bufferedTransitionPrefix C j ^ j,
    fun j => mul_nonneg (mul_nonneg (by positivity) (hR j))
      (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hC j)) j), ?_⟩
  intro S O hO hS hSpos hSb j x hx
  have hzero : S x ≤ max 0 (C 0) := by
    have h := hSb 0 x hx
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hSpos x hx)] at h
    exact h.trans (le_max_right _ _)
  have hout (k : ℕ) (hkj : k ≤ j) :
      ‖iteratedFDerivWithin ℝ k tensorCoverageDenominator univ (S x)‖ ≤ R j := by
    rw [iteratedFDerivWithin_univ]
    exact hscalar j k hkj (S x) ⟨hSpos x hx, hzero⟩
  have hin (k : ℕ) (hk : 1 ≤ k) (hkj : k ≤ j) :
      ‖iteratedFDerivWithin ℝ k S O x‖ ≤ bufferedTransitionPrefix C j ^ k := by
    rw [iteratedFDerivWithin_of_isOpen _ hO hx]
    have hc : C k ≤ bufferedTransitionPrefix C j := by
      have hsum : C k ≤ ∑ i ∈ Finset.range (j + 1), C i :=
        Finset.single_le_sum (fun i _ => hC i) (by simpa using hkj)
      unfold bufferedTransitionPrefix
      linarith
    exact (hSb k x hx).trans (hc.trans (le_self_pow₀ (one_le_bufferedTransitionPrefix hC j) (by omega)))
  have h := norm_iteratedFDerivWithin_comp_le tensorCoverageDenominator_contDiff.contDiffOn hS
    (n := j) (by simp) uniqueDiffOn_univ hO.uniqueDiffOn (mapsTo_univ _ _) hx hout hin
  rwa [iteratedFDerivWithin_of_isOpen _ hO hx] at h

/-- Exact scale factor in the actual square sum. -/
theorem tensorLocalCoverageSum_eq_four_mul {ι X : Type*} [Fintype ι]
    (b : ι → X → ℝ) (x : X) :
    tensorLocalCoverageSum b x = 4 * squareCutoffSum b x := by
  unfold tensorLocalCoverageSum squareCutoffSum
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  ring

/-- Every derivative of multiplication by a fixed real scalar has the same
scalar norm factor, on genuine open domains. -/
theorem tensor_const_mul_jet_norm {f : E → ℝ} {O : Set E}
    (hO : IsOpen O) (hf : ContDiffOn ℝ ∞ f O) {x : E} (hx : x ∈ O) (a : ℝ) (j : ℕ) :
    ‖iteratedFDeriv ℝ j (fun y => a * f y) x‖ = |a| * ‖iteratedFDeriv ℝ j f x‖ := by
  change ‖iteratedFDeriv ℝ j (fun y => a • f y) x‖ = _
  rw [iteratedFDeriv_const_smul_apply' ((hf.contDiffAt (hO.mem_nhds hx)).of_le (by simp)), norm_smul,
    Real.norm_eq_abs]

variable {X : Type*} [TopologicalSpace X]

/-- The local-cover normalized cutoff has a uniform true all-order
receiving-coordinate derivative profile derived solely from the original raw
profile and actual overlap D. The raw family need NOT cover all of X.
The statement allows c to be continuous only on the real open chart domain. -/
theorem exists_tensorLocalNormalizedCutoff_derivative_bounds
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (D : ℕ) :
    ∃ N : ℕ → ℝ, (∀ j, 0 ≤ N j) ∧
      ∀ (ι : Type*) [Fintype ι] (b : ι → X → ℝ) (c : E → X) (O : Set E), IsOpen O →
      (∀ i, ContDiffOn ℝ ∞ (b i ∘ c) O) → ContinuousOn c O →
      (∀ x ∈ O, (activeCutoffIndices b (c x)).card ≤ D) →
      (∀ i, ∀ x ∈ O, c x ∈ tsupport (b i) →
        ∀ j, ‖iteratedFDeriv ℝ j (b i ∘ c) x‖ ≤ B j) →
      ∀ i j, ∀ x ∈ O, ‖iteratedFDeriv ℝ j (tensorLocalNormalizedCutoff b i ∘ c) x‖ ≤ N j := by
  obtain ⟨C, hC, hsum⟩ := exists_squareCutoffSum_bounds_of_multiplicity (E := E) (X := X) B hB D
  obtain ⟨Q, hQ, hcomp⟩ := exists_tensorCoverageDenominator_composition_bounds
    (E := E) (fun j => 4 * C j) (fun j => mul_nonneg (by norm_num) (hC j))
  obtain ⟨N, hN, hnormalize⟩ := exists_squareNormalizedCutoff_derivative_bounds
    (E := E) (fun j => 2 * B j) Q (fun j => mul_nonneg (by norm_num) (hB j)) hQ
  refine ⟨N, hN, ?_⟩
  intro ι _ b c O hO hb hc hD hbBound
  have hS : ContDiffOn ℝ ∞ (squareCutoffSum b ∘ c) O :=
    ContDiffOn.sum (fun i _ => (hb i).pow 2)
  have hscaled : ContDiffOn ℝ ∞ (tensorLocalCoverageSum b ∘ c) O :=
    ContDiffOn.sum (fun i _ => (contDiffOn_const.mul (hb i)).pow 2)
  have hCb (j : ℕ) (x : E) (hx : x ∈ O) :
      ‖iteratedFDeriv ℝ j (squareCutoffSum b ∘ c) x‖ ≤ C j := by
    have h := hsum ι 1 zero_le_one b c O hO hb x hx (hc.continuousAt (hO.mem_nhds hx)) (hD x hx)
      (fun i hi k => by simpa only [one_pow, mul_one] using hbBound i x hx hi k) j
    simpa only [one_pow, mul_one] using h
  have hscaledEq : tensorLocalCoverageSum b ∘ c = fun y => 4 * (squareCutoffSum b ∘ c) y :=
    funext (fun y => tensorLocalCoverageSum_eq_four_mul b (c y))
  have hScaledBound (j : ℕ) (x : E) (hx : x ∈ O) :
      ‖iteratedFDeriv ℝ j (tensorLocalCoverageSum b ∘ c) x‖ ≤ 4 * C j := by
    rw [hscaledEq, tensor_const_mul_jet_norm hO hS hx]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul_of_nonneg_left (hCb j x hx) (by norm_num)
  have hdenEq : squareCutoffSum (fun a => tensorLocalAugmentedRaw b a ∘ c) =
      tensorCoverageDenominator ∘ (tensorLocalCoverageSum b ∘ c) :=
    funext (fun y => tensorLocalAugmentedRaw_square_sum b (c y))
  have hdenBound (j : ℕ) (x : E) (hx : x ∈ O) :
      ‖iteratedFDeriv ℝ j (squareCutoffSum (fun a => tensorLocalAugmentedRaw b a ∘ c)) x‖ ≤ Q j := by
    rw [hdenEq]
    exact hcomp _ O hO hscaled (fun y _ => tensorLocalCoverageSum_nonneg b (c y)) hScaledBound j x hx
  have haug (a : Option ι) : ContDiffOn ℝ ∞ (tensorLocalAugmentedRaw b a ∘ c) O := by
    cases a with
    | none => exact tensorCoverageBump.contDiff.comp_contDiffOn hscaled
    | some i => exact contDiffOn_const.mul (hb i)
  intro i j x hx
  have hnum (k : ℕ) (y : E) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (tensorLocalAugmentedRaw b (some i) ∘ c) y‖ ≤ (2 * B k) * 1 ^ k := by
    change ‖iteratedFDeriv ℝ k (fun z => 2 * (b i ∘ c) z) y‖ ≤ _
    rw [tensor_const_mul_jet_norm hO (hb i) hy]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), one_pow, mul_one]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    by_cases hi : c y ∈ tsupport (b i)
    · exact hbBound i y hy hi k
    · rw [iteratedFDeriv_comp_eq_zero_off_tsupport (b i) c y
        (hc.continuousAt (hO.mem_nhds hy)) hi k, norm_zero]
      exact hB k
  have h := hnormalize (Option ι) 1 le_rfl (fun a => tensorLocalAugmentedRaw b a ∘ c)
    O hO haug (fun y _ => tensorLocalAugmentedRaw_one_le b (c y))
    (fun k y hy => by simpa only [one_pow, mul_one] using hdenBound k y hy) (some i) hnum j x hx
  have heq : squareNormalizedCutoff (fun a => tensorLocalAugmentedRaw b a ∘ c) (some i) =
      tensorLocalNormalizedCutoff b i ∘ c := by
    funext y
    rfl
  rw [heq] at h
  simpa only [one_pow, mul_one] using h

end
end GlobalEmbedding.Offline
