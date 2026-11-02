import Probes.ActualRefinementBumpJets
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

/-!
# A fixed globally smooth normalization with no support-boundary singularity

The denominator equals the original sum once that sum is at least one half,
and stays at least one quarter everywhere. Thus the actual cutoffs are smooth
also where every raw bump vanishes; no regularity of inactive phases is used.
-/

noncomputable section
open Set Function Metric
open scoped ContDiff Topology BigOperators
namespace GlobalEmbedding.Continuation

def actualRefinementDenominator (s : ℝ) : ℝ :=
  1+Real.smoothTransition (4*s-1)*(s-1)

theorem actualRefinementDenominator_contDiff : ContDiff ℝ ∞ actualRefinementDenominator := by
  have ht : ContDiff ℝ ∞ (fun s : ℝ => Real.smoothTransition (4*s-1)) :=
    (Real.smoothTransition.contDiff : ContDiff ℝ ∞ Real.smoothTransition).comp
      ((contDiff_const.mul contDiff_id).sub contDiff_const)
  exact contDiff_const.add (ht.mul (contDiff_id.sub contDiff_const))

theorem actualRefinementDenominator_lower (s : ℝ) : (1:ℝ)/4 ≤ actualRefinementDenominator s := by
  have hn := Real.smoothTransition.nonneg (4*s-1)
  have hu := Real.smoothTransition.le_one (4*s-1)
  by_cases hs : s ≤ 1/4
  · rw [actualRefinementDenominator,Real.smoothTransition.zero_of_nonpos (by linarith)]
    norm_num
  · have hs0 : 1/4 < s := lt_of_not_ge hs
    by_cases hs1 : s ≤ 1
    · have hh := mul_le_mul_of_nonpos_right hu (sub_nonpos.mpr hs1)
      unfold actualRefinementDenominator
      nlinarith only [hh,hs0]
    · have hh := mul_nonneg hn (sub_nonneg.mpr (le_of_not_ge hs1))
      unfold actualRefinementDenominator
      linarith

theorem actualRefinementDenominator_eq (s : ℝ) (hs : 1/2 ≤ s) :
    actualRefinementDenominator s = s := by
  rw [actualRefinementDenominator,Real.smoothTransition.one_of_one_le (by linarith)]
  ring

theorem actualRefinementDenominator_ge (s : ℝ) : s ≤ actualRefinementDenominator s := by
  by_cases hs : 1/2 ≤ s
  · rw [actualRefinementDenominator_eq s hs]
  · have hu := Real.smoothTransition.le_one (4*s-1)
    have hh := mul_le_mul_of_nonpos_right hu (by linarith : s-1 ≤ 0)
    unfold actualRefinementDenominator
    nlinarith only [hh]

def actualRefinementReciprocal (s : ℝ) : ℝ := (actualRefinementDenominator s)⁻¹

theorem actualRefinementReciprocal_contDiff : ContDiff ℝ ∞ actualRefinementReciprocal :=
  actualRefinementDenominator_contDiff.inv (fun s =>
    (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4) (actualRefinementDenominator_lower s)).ne')

theorem actualRefinementReciprocal_nonneg (s : ℝ) : 0 ≤ actualRefinementReciprocal s :=
  inv_nonneg.mpr ((show (0:ℝ) ≤ 1/4 by norm_num).trans (actualRefinementDenominator_lower s))

theorem actualRefinementReciprocal_exact (s : ℝ) (hs : 1/2 ≤ s) :
    s*actualRefinementReciprocal s = 1 := by
  unfold actualRefinementReciprocal
  rw [actualRefinementDenominator_eq s hs,mul_inv_cancel₀ (by linarith : s ≠ 0)]

theorem actualRefinementReciprocal_subunit (s : ℝ) : s*actualRefinementReciprocal s ≤ 1 := by
  change s*(actualRefinementDenominator s)⁻¹ ≤ 1
  rw [← div_eq_mul_inv]
  exact (div_le_one₀ (lt_of_lt_of_le (by norm_num : (0:ℝ) < 1/4)
    (actualRefinementDenominator_lower s))).2 (actualRefinementDenominator_ge s)

theorem actual_refinement_reciprocal_derivatives_bounded (R : ℝ) (j : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x ∈ closedBall (0:ℝ) R,
      ‖iteratedFDeriv ℝ j actualRefinementReciprocal x‖ ≤ C := by
  have hb := (isCompact_closedBall (0:ℝ) R).bddAbove_image
    ((actualRefinementReciprocal_contDiff.continuous_iteratedFDeriv
      (by simp : (j : ℕ∞ω) ≤ ∞)).norm.continuousOn)
  obtain ⟨C,hC⟩ := hb
  exact ⟨max C 0,le_max_right _ _,fun x hx =>
    (hC (Set.mem_image_of_mem _ hx)).trans (le_max_left _ _)⟩

def actualRefinementReciprocalDerivativeCost (R : ℝ) (j : ℕ) : ℝ :=
  Classical.choose (actual_refinement_reciprocal_derivatives_bounded R j)

theorem actualRefinementReciprocalDerivativeCost_nonneg (R : ℝ) (j : ℕ) :
    0 ≤ actualRefinementReciprocalDerivativeCost R j :=
  (Classical.choose_spec (actual_refinement_reciprocal_derivatives_bounded R j)).1

theorem actualRefinementReciprocalDerivativeCost_bound (R : ℝ) (j : ℕ)
    (x : ℝ) (hx : ‖x‖ ≤ R) :
    ‖iteratedFDeriv ℝ j actualRefinementReciprocal x‖ ≤ actualRefinementReciprocalDerivativeCost R j :=
  (Classical.choose_spec (actual_refinement_reciprocal_derivatives_bounded R j)).2 x
    (by simpa only [mem_closedBall,dist_zero_right] using hx)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualRefinementReciprocal_contDiff
#print axioms GlobalEmbedding.Continuation.actualRefinementReciprocal_exact
#print axioms GlobalEmbedding.Continuation.actual_refinement_reciprocal_derivatives_bounded
