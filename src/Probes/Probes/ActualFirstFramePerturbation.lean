import Probes.ActualSpatialJointJets

/-!
# Quantitative preservation of the actual first-derivative frame

This is the native perturbation estimate needed when replacing a map by its
actual smoothing. The source inclusion costs at most one. A squared singular
reserve c survives with c/4 whenever the actual first-derivative operator
changes by at most sqrt(c)/2. No immersion of the perturbed map is assumed.
-/

noncomputable section
open Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {E V : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup V] [NormedSpace ℝ V]

theorem actual_first_frame_reserve_perturbation
    (A B : E →L[ℝ] V) (c : ℝ) (hc : 0 < c)
    (hA : ∀ v, c * ‖v‖^2 ≤ ‖A v‖^2)
    (hBA : ‖B-A‖ ≤ Real.sqrt c / 2) :
    ∀ v, (c/4) * ‖v‖^2 ≤ ‖B v‖^2 := by
  intro v
  have hsqrt := Real.sq_sqrt hc.le
  have hfirst : Real.sqrt c * ‖v‖ ≤ ‖A v‖ := by
    apply (sq_le_sq₀ (mul_nonneg (Real.sqrt_nonneg _) (norm_nonneg _)) (norm_nonneg _)).mp
    simpa only [mul_pow, hsqrt] using hA v
  have htriangle : ‖A v‖ ≤ ‖B v‖ + (Real.sqrt c / 2) * ‖v‖ := by
    calc
      _ = ‖B v - (B-A) v‖ := by simp
      _ ≤ ‖B v‖ + ‖(B-A) v‖ := norm_sub_le _ _
      _ ≤ ‖B v‖ + ‖B-A‖ * ‖v‖ := add_le_add le_rfl ((B-A).le_opNorm v)
      _ ≤ _ := add_le_add le_rfl (mul_le_mul_of_nonneg_right hBA (norm_nonneg v))
  have hsecond : (Real.sqrt c / 2) * ‖v‖ ≤ ‖B v‖ := by linarith
  have hsq := (sq_le_sq₀
    (mul_nonneg (div_nonneg (Real.sqrt_nonneg _) (by norm_num)) (norm_nonneg _))
    (norm_nonneg _)).mpr hsecond
  calc
    (c/4) * ‖v‖^2 = ((Real.sqrt c / 2) * ‖v‖)^2 := by
      rw [mul_pow,div_pow,hsqrt]
      norm_num
    _ ≤ _ := hsq

theorem actual_first_frame_injective_of_reserve
    (A : E →L[ℝ] V) (c : ℝ) (hc : 0 < c)
    (hA : ∀ v, c * ‖v‖^2 ≤ ‖A v‖^2) : Function.Injective A := by
  apply (injective_iff_map_eq_zero A).mpr
  intro v hv
  by_contra hv0
  have hp : 0 < c * ‖v‖^2 := mul_pos hc (sq_pos_of_pos (norm_pos_iff.mpr hv0))
  exact (not_le_of_gt hp) (by simpa [hv] using hA v)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actual_first_frame_reserve_perturbation
#print axioms GlobalEmbedding.Continuation.actual_first_frame_injective_of_reserve
