import Smoothing.Round4CutoffFiniteBounds

/-!
# Finite raw costs for the actual local-parameter normalization

The auxiliary denominator is the same fixed scalar coverage repair used in
TensorLocalNormalization. It is not an extra parameter chart. Its scalar
derivative bound is selected using only the zeroth-order square-sum bound.
Consequently the j-th normalized cutoff bound reads raw jets only through j.
-/

open GlobalEmbedding.Offline Function Set Filter
open scoped ContDiff Topology BigOperators

namespace GlobalEmbedding.Continuation
noncomputable section
set_option backward.isDefEq.respectTransparency false

def round4CoverageScalarBound (C0 : ℝ) : ℕ → ℝ :=
  Classical.choose (exists_tensorCoverageDenominator_derivative_bounds C0)

theorem round4CoverageScalarBound_nonneg (C0 : ℝ) (j : ℕ) :
    0 ≤ round4CoverageScalarBound C0 j :=
  (Classical.choose_spec (exists_tensorCoverageDenominator_derivative_bounds C0)).1 j

theorem round4CoverageScalarBound_spec (C0 : ℝ) (j k : ℕ) (hkj : k ≤ j)
    (s : ℝ) (hs : s ∈ Icc 0 (max 0 C0)) :
    ‖iteratedFDeriv ℝ k tensorCoverageDenominator s‖ ≤ round4CoverageScalarBound C0 j :=
  (Classical.choose_spec (exists_tensorCoverageDenominator_derivative_bounds C0)).2 j k hkj s hs

def round4CoverageProfile (C : ℕ → ℝ) (j : ℕ) : ℝ :=
  (j.factorial : ℝ) * round4CoverageScalarBound (C 0) j *
    bufferedTransitionPrefix C j ^ j

theorem round4CoverageProfile_nonneg {C : ℕ → ℝ}
    (hC : ∀ j, 0 ≤ C j) (j : ℕ) : 0 ≤ round4CoverageProfile C j :=
  mul_nonneg (mul_nonneg (by positivity) (round4CoverageScalarBound_nonneg _ _))
    (pow_nonneg (zero_le_one.trans (one_le_bufferedTransitionPrefix hC j)) j)

theorem round4CoverageProfile_congr_prefix {C₁ C₂ : ℕ → ℝ} (j : ℕ)
    (hC : ∀ a ≤ j, C₁ a = C₂ a) :
    round4CoverageProfile C₁ j = round4CoverageProfile C₂ j := by
  unfold round4CoverageProfile
  rw [hC 0 (Nat.zero_le j), parameterTransitionPrefix_congr j hC]

/-- The two original factors 2 and 4 from the actual local normalization. -/
def round4LocalNormalizationProfile (B : ℕ → ℝ) (D : ℕ) : ℕ → ℝ :=
  round4NormalizationProfile (fun j => 2 * B j)
    (round4CoverageProfile (fun j => 4 * round4SquareSumProfile D B j))

theorem round4LocalNormalizationProfile_nonneg {B : ℕ → ℝ}
    (hB : ∀ j, 0 ≤ B j) (D j : ℕ) : 0 ≤ round4LocalNormalizationProfile B D j :=
  round4NormalizationProfile_nonneg (fun k => mul_nonneg (by norm_num) (hB k))
    (round4CoverageProfile_nonneg (fun k => mul_nonneg (by norm_num)
      (round4SquareSumProfile_nonneg D hB k))) j

theorem round4LocalNormalizationProfile_congr_prefix {B₁ B₂ : ℕ → ℝ} (D j : ℕ)
    (hB : ∀ a ≤ j, B₁ a = B₂ a) :
    round4LocalNormalizationProfile B₁ D j = round4LocalNormalizationProfile B₂ D j := by
  apply round4NormalizationProfile_congr_prefix j
  · intro a ha
    rw [hB a ha]
  · intro a ha
    apply round4CoverageProfile_congr_prefix a
    intro k hk
    rw [round4SquareSumProfile_congr_prefix D k (fun l hl => hB l (hl.trans (hk.trans ha)))]

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem round4_coverage_composition_jet_bound
    (C : ℕ → ℝ) (hC : ∀ j, 0 ≤ C j)
    (S : E → ℝ) (O : Set E) (hO : IsOpen O) (hS : ContDiffOn ℝ ∞ S O)
    (hpos : ∀ x ∈ O, 0 ≤ S x)
    (hbound : ∀ k, ∀ x ∈ O, ‖iteratedFDeriv ℝ k S x‖ ≤ C k)
    (j : ℕ) (x : E) (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ j (tensorCoverageDenominator ∘ S) x‖ ≤ round4CoverageProfile C j := by
  have hupper : S x ≤ max 0 (C 0) := by
    have hzero := hbound 0 x hx
    simp only [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_of_nonneg (hpos x hx)] at hzero
    exact hzero.trans (le_max_right _ _)
  exact parameter_general_composition_jet_le C hC hO isOpen_univ hS
    tensorCoverageDenominator_contDiff.contDiffOn (mapsTo_univ _ _) hx j
    (round4CoverageScalarBound (C 0) j)
    (fun k hk => round4CoverageScalarBound_spec (C 0) j k hk (S x) ⟨hpos x hx,hupper⟩)
    (fun k _ _ => hbound k x hx)

variable {X : Type*} [TopologicalSpace X]

/-- Actual local normalized jets with an explicit finite raw profile.
No global parameter cover and no output-bound hypothesis is used. -/
theorem round4_local_normalized_cutoff_jet_bound
    (B : ℕ → ℝ) (hB : ∀ j, 0 ≤ B j) (D : ℕ)
    {ι : Type*} [Fintype ι] (b : ι → X → ℝ) (c : E → X) (O : Set E)
    (hO : IsOpen O) (hb : ∀ i, ContDiffOn ℝ ∞ (b i ∘ c) O) (hc : ContinuousOn c O)
    (hD : ∀ x ∈ O, (activeCutoffIndices b (c x)).card ≤ D)
    (hbound : ∀ i, ∀ x ∈ O, c x ∈ tsupport (b i) → ∀ k,
      ‖iteratedFDeriv ℝ k (b i ∘ c) x‖ ≤ B k)
    (i : ι) (j : ℕ) (x : E) (hx : x ∈ O) :
    ‖iteratedFDeriv ℝ j (tensorLocalNormalizedCutoff b i ∘ c) x‖ ≤
      round4LocalNormalizationProfile B D j := by
  let C := round4SquareSumProfile D B
  have hC : ∀ k, 0 ≤ C k := round4SquareSumProfile_nonneg D hB
  have hS : ContDiffOn ℝ ∞ (squareCutoffSum b ∘ c) O :=
    ContDiffOn.sum (fun a _ => (hb a).pow 2)
  have hCb (k : ℕ) (y : E) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (squareCutoffSum b ∘ c) y‖ ≤ C k :=
    round4_square_sum_jet_bound B hB D b c O hO hb y hy
      (hc.continuousAt (hO.mem_nhds hy)) (hD y hy) (fun a ha => hbound a y hy ha) k
  have hscaled : ContDiffOn ℝ ∞ (tensorLocalCoverageSum b ∘ c) O :=
    ContDiffOn.sum (fun a _ => (contDiffOn_const.mul (hb a)).pow 2)
  have hscaledEq : tensorLocalCoverageSum b ∘ c = fun y => 4 * (squareCutoffSum b ∘ c) y :=
    funext (fun y => tensorLocalCoverageSum_eq_four_mul b (c y))
  have hScaledBound (k : ℕ) (y : E) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (tensorLocalCoverageSum b ∘ c) y‖ ≤ 4 * C k := by
    rw [hscaledEq,tensor_const_mul_jet_norm hO hS hy]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 4)]
    exact mul_le_mul_of_nonneg_left (hCb k y hy) (by norm_num)
  let Q := round4CoverageProfile (fun k => 4 * C k)
  have hQ : ∀ k, 0 ≤ Q k :=
    round4CoverageProfile_nonneg (fun k => mul_nonneg (by norm_num) (hC k))
  have hdenEq : squareCutoffSum (fun a => tensorLocalAugmentedRaw b a ∘ c) =
      tensorCoverageDenominator ∘ (tensorLocalCoverageSum b ∘ c) :=
    funext (fun y => tensorLocalAugmentedRaw_square_sum b (c y))
  have hdenBound (k : ℕ) (y : E) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (squareCutoffSum (fun a => tensorLocalAugmentedRaw b a ∘ c)) y‖ ≤ Q k := by
    rw [hdenEq]
    exact round4_coverage_composition_jet_bound (fun k => 4 * C k)
      (fun k => mul_nonneg (by norm_num) (hC k)) _ O hO hscaled
      (fun z _ => tensorLocalCoverageSum_nonneg b (c z)) hScaledBound k y hy
  have haug (a : Option ι) : ContDiffOn ℝ ∞ (tensorLocalAugmentedRaw b a ∘ c) O := by
    cases a with
    | none => exact tensorCoverageBump.contDiff.comp_contDiffOn hscaled
    | some a => exact contDiffOn_const.mul (hb a)
  have hnum (k : ℕ) (y : E) (hy : y ∈ O) :
      ‖iteratedFDeriv ℝ k (tensorLocalAugmentedRaw b (some i) ∘ c) y‖ ≤ 2 * B k := by
    change ‖iteratedFDeriv ℝ k (fun z => 2 * (b i ∘ c) z) y‖ ≤ _
    rw [tensor_const_mul_jet_norm hO (hb i) hy]
    norm_num only [abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
    apply mul_le_mul_of_nonneg_left _ (by norm_num)
    by_cases hi : c y ∈ tsupport (b i)
    · exact hbound i y hy hi k
    · rw [iteratedFDeriv_comp_eq_zero_off_tsupport (b i) c y
        (hc.continuousAt (hO.mem_nhds hy)) hi k,norm_zero]
      exact hB k
  exact round4_normalized_cutoff_jet_bound (fun k => 2 * B k) Q
    (fun k => mul_nonneg (by norm_num) (hB k)) hQ
    (fun a => tensorLocalAugmentedRaw b a ∘ c) O hO haug
    (fun y _ => tensorLocalAugmentedRaw_one_le b (c y)) hdenBound (some i) hnum j x hx

#print axioms round4_local_normalized_cutoff_jet_bound
#print axioms round4LocalNormalizationProfile_congr_prefix
end
end GlobalEmbedding.Continuation
