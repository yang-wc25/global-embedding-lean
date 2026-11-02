import Initialization.Geometry.CoframeFreezing

/-!
# Centered rescaling of genuine local fields

The constants come from smoothness on a fixed compact coordinate domain.
The exact identities use affine equivalences, so arbitrary off-domain values
of chart representatives do not affect the result. No global smooth extension
is required. This is the rate-control step in `prop:initialization`, 816--821.
-/

open Set
open scoped ContDiff

namespace GlobalEmbedding.Initialization

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- Exact all-order derivative under a centered inverse dilation. -/
theorem iteratedFDeriv_centered_rescaling (f : E → F) (q : E)
    {T : ℝ} (hT : T ≠ 0) (j : ℕ) (y : E) :
    iteratedFDeriv ℝ j (fun z ↦ f (q + T⁻¹ • z)) y =
      (T⁻¹) ^ j • iteratedFDeriv ℝ j f (q + T⁻¹ • y) := by
  let a : E ≃L[ℝ] E := ContinuousLinearEquiv.smulLeft (Units.mk0 T⁻¹ (inv_ne_zero hT))
  let g : E → F := fun z ↦ f (q + z)
  have ha : iteratedFDeriv ℝ j (g ∘ a) y =
      (iteratedFDeriv ℝ j g (a y)).compContinuousLinearMap (fun _ ↦ a) := by
    simpa only [Set.preimage_univ, iteratedFDerivWithin_univ] using
      a.iteratedFDerivWithin_comp_right g uniqueDiffOn_univ (Set.mem_univ _) j
  change iteratedFDeriv ℝ j (g ∘ a) y = _
  rw [ha]
  have hg : iteratedFDeriv ℝ j g (a y) = iteratedFDeriv ℝ j f (q + a y) :=
    iteratedFDeriv_comp_add_left j q (a y)
  rw [hg]
  ext v
  simp only [ContinuousMultilinearMap.compContinuousLinearMap_apply, smul_apply]
  change (iteratedFDeriv ℝ j f (q + T⁻¹ • y)) (fun i ↦ T⁻¹ • v i) = _
  rw [ContinuousMultilinearMap.map_smul_univ]
  simp

/-- A genuine smooth local field has one derivative-bound sequence for every
center and every scale. Positive-order rescaled derivatives retain the full
factor T⁻ʲ. The constant sequence is selected before q,T and the evaluation point. -/
theorem exists_centered_rescaling_bounds
    {s O : Set E} (hs : IsCompact s) (hO : IsOpen O) (hsO : s ⊆ O)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (q : E) (T : ℝ), 1 ≤ T → ∀ j y, q + T⁻¹ • y ∈ s →
        ‖iteratedFDeriv ℝ j (fun z ↦ f (q + T⁻¹ • z)) y‖ ≤ B j * (T⁻¹) ^ j := by
  obtain ⟨B, hB, hbound⟩ := exists_compact_smooth_derivative_bounds hs hO hsO f hf
  refine ⟨B, hB, ?_⟩
  intro q T hT j y hy
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  rw [iteratedFDeriv_centered_rescaling f q hTpos.ne', norm_smul,
    Real.norm_eq_abs, abs_of_nonneg (pow_nonneg (inv_nonneg.mpr hTpos.le) _)]
  exact (mul_le_mul_of_nonneg_left (hbound j _ hy) (by positivity)).trans_eq (mul_comm _ _)

/-- Every positive-order rescaled derivative is O(T⁻¹), uniformly in the
center and scale, as used for the coframe-rate discrepancy in the manuscript. -/
theorem exists_centered_rescaling_positive_order_bounds
    {s O : Set E} (hs : IsCompact s) (hO : IsOpen O) (hsO : s ⊆ O)
    (f : E → F) (hf : ContDiffOn ℝ ∞ f O) :
    ∃ B : ℕ → ℝ, (∀ j, 0 ≤ B j) ∧
      ∀ (q : E) (T : ℝ), 1 ≤ T → ∀ j, 1 ≤ j →
      ∀ y, q + T⁻¹ • y ∈ s →
        ‖iteratedFDeriv ℝ j (fun z ↦ f (q + T⁻¹ • z)) y‖ ≤ B j / T := by
  obtain ⟨B, hB, hbound⟩ := exists_centered_rescaling_bounds hs hO hsO f hf
  refine ⟨B, hB, ?_⟩
  intro q T hT j hj y hy
  have hTpos : 0 < T := zero_lt_one.trans_le hT
  calc
    ‖iteratedFDeriv ℝ j (fun z ↦ f (q + T⁻¹ • z)) y‖ ≤ B j * (T⁻¹) ^ j :=
      hbound q T hT j y hy
    _ ≤ B j * T⁻¹ := mul_le_mul_of_nonneg_left
      (pow_le_of_le_one (inv_nonneg.mpr hTpos.le) (inv_le_one_of_one_le₀ hT)
        (by omega)) (hB j)
    _ = B j / T := (div_eq_mul_inv _ _).symm

/-- The positive-order derivatives of a frozen coframe error are precisely the
negative derivatives of that coframe. The statement only requires smoothness
at the actual chart point, not outside the chart. -/
theorem iteratedFDeriv_frozen_error_rescaled
    (f : E → F) (p q : E) {T : ℝ} (hT : T ≠ 0) {j : ℕ} (hj : j ≠ 0)
    (y : E) (hf : ContDiffAt ℝ j f (q + T⁻¹ • y)) :
    iteratedFDeriv ℝ j (fun z ↦ f p - f (q + T⁻¹ • z)) y =
      -((T⁻¹) ^ j • iteratedFDeriv ℝ j f (q + T⁻¹ • y)) := by
  rw [iteratedFDeriv_centered_rescaling (fun z ↦ f p - f z) q hT]
  have hsub : iteratedFDeriv ℝ j (fun z ↦ f p - f z) (q + T⁻¹ • y) =
      -iteratedFDeriv ℝ j f (q + T⁻¹ • y) := by
    change iteratedFDeriv ℝ j ((fun _ : E ↦ f p) - f) (q + T⁻¹ • y) = _
    rw [iteratedFDeriv_sub_apply contDiffAt_const hf, iteratedFDeriv_const_of_ne hj]
    simp
  rw [hsub, smul_neg]

end GlobalEmbedding.Initialization
