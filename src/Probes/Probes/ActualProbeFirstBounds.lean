import Probes.ActualProbeScaleBounds

/-!
# The actual probe columns have the original value and first-derivative sizes

Source: the first two bounds in (8.2), before the homogeneous and secondary
corrections and infinite repair tail. Both columns are the actual functions
used by `ActualFiniteProbeResponse`, and all first derivatives are native.
-/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- First derivative norm of the literal cosine-amplitude wave. -/
theorem norm_fderiv_cos_smul_le {θ : E → ℝ} {A : E → F} (x : E)
    (hθ : DifferentiableAt ℝ θ x) (hA : DifferentiableAt ℝ A x) :
    ‖fderiv ℝ (fun y ↦ Real.cos (θ y) • A y) x‖ ≤
      ‖fderiv ℝ A x‖ + ‖fderiv ℝ θ x‖ * ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [fderiv_cos_smul_apply hθ hA]
  calc
    _ ≤ ‖Real.cos (θ x) • fderiv ℝ A x w‖ +
        ‖(Real.sin (θ x) * fderiv ℝ θ x w) • A x‖ := norm_sub_le _ _
    _ ≤ ‖fderiv ℝ A x w‖ + ‖fderiv ℝ θ x w‖ * ‖A x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul]
      gcongr
      · exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)
      · exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one _)
    _ ≤ (‖fderiv ℝ A x‖ * ‖w‖) + (‖fderiv ℝ θ x‖ * ‖w‖) * ‖A x‖ := by
      gcongr
      · exact (fderiv ℝ A x).le_opNorm w
      · exact (fderiv ℝ θ x).le_opNorm w
    _ = _ := by ring

/-- The sine partner obeys the identical first-derivative bound. -/
theorem norm_fderiv_sin_smul_le {θ : E → ℝ} {A : E → F} (x : E)
    (hθ : DifferentiableAt ℝ θ x) (hA : DifferentiableAt ℝ A x) :
    ‖fderiv ℝ (fun y ↦ Real.sin (θ y) • A y) x‖ ≤
      ‖fderiv ℝ A x‖ + ‖fderiv ℝ θ x‖ * ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro w
  rw [fderiv_sin_smul_apply hθ hA]
  calc
    _ ≤ ‖Real.sin (θ x) • fderiv ℝ A x w‖ +
        ‖(Real.cos (θ x) * fderiv ℝ θ x w) • A x‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ A x w‖ + ‖fderiv ℝ θ x w‖ * ‖A x‖ := by
      simp only [norm_smul, Real.norm_eq_abs, abs_mul]
      gcongr
      · exact mul_le_of_le_one_left (by positivity) (Real.abs_sin_le_one _)
      · exact mul_le_of_le_one_left (by positivity) (Real.abs_cos_le_one _)
    _ ≤ (‖fderiv ℝ A x‖ * ‖w‖) + (‖fderiv ℝ θ x‖ * ‖w‖) * ‖A x‖ := by
      gcongr
      · exact (fderiv ℝ A x).le_opNorm w
      · exact (fderiv ℝ θ x).le_opNorm w
    _ = _ := by ring

/-- The genuine leading value column is bounded at the original `a=δτ` scale. -/
theorem norm_actualProbeCosColumn_le (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) :
    ‖actualProbeCosColumn δ τ lam ψ A x‖ ≤ |δ * τ / lam ^ 2| * ‖A x‖ := by
  simp only [actualProbeCosColumn, norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _)

/-- The same original value bound for the sine partner. -/
theorem norm_actualProbeSinColumn_le (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) :
    ‖actualProbeSinColumn δ τ lam ψ A x‖ ≤ |δ * τ / lam ^ 2| * ‖A x‖ := by
  simp only [actualProbeSinColumn, norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  exact mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _)

/-- First derivative estimate for the actual scaled cosine column. -/
theorem norm_fderiv_actualProbeCosColumn_le {ψ : E → ℝ} {A : E → F}
    (x : E) (hψ : DifferentiableAt ℝ ψ x) (hA : DifferentiableAt ℝ A x)
    (δ τ lam : ℝ) :
    ‖fderiv ℝ (actualProbeCosColumn δ τ lam ψ A) x‖ ≤
      |δ * τ / lam ^ 2| * (‖fderiv ℝ A x‖ + |lam / τ| * ‖fderiv ℝ ψ x‖ * ‖A x‖) := by
  have hθ : DifferentiableAt ℝ (probeFastPhase τ lam ψ) x := hψ.const_smul (lam / τ)
  have hmod : DifferentiableAt ℝ (fun y ↦ Real.cos (probeFastPhase τ lam ψ y) • A y) x :=
    hθ.cos.smul hA
  unfold actualProbeCosColumn
  rw [fderiv_fun_const_smul hmod, norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h := norm_fderiv_cos_smul_le x hθ hA
  rw [fderiv_probeFastPhase hψ, norm_smul, Real.norm_eq_abs] at h
  simpa only [mul_assoc] using h

/-- First derivative estimate for the actual scaled sine column. -/
theorem norm_fderiv_actualProbeSinColumn_le {ψ : E → ℝ} {A : E → F}
    (x : E) (hψ : DifferentiableAt ℝ ψ x) (hA : DifferentiableAt ℝ A x)
    (δ τ lam : ℝ) :
    ‖fderiv ℝ (actualProbeSinColumn δ τ lam ψ A) x‖ ≤
      |δ * τ / lam ^ 2| * (‖fderiv ℝ A x‖ + |lam / τ| * ‖fderiv ℝ ψ x‖ * ‖A x‖) := by
  have hθ : DifferentiableAt ℝ (probeFastPhase τ lam ψ) x := hψ.const_smul (lam / τ)
  have hmod : DifferentiableAt ℝ (fun y ↦ Real.sin (probeFastPhase τ lam ψ y) • A y) x :=
    hθ.sin.smul hA
  unfold actualProbeSinColumn
  rw [fderiv_fun_const_smul hmod, norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  have h := norm_fderiv_sin_smul_le x hθ hA
  rw [fderiv_probeFastPhase hψ, norm_smul, Real.norm_eq_abs] at h
  simpa only [mul_assoc] using h

/-- The scalar reduction for the original first-derivative scale. -/
theorem probe_first_scale_inequality
    (δ τ ell lam K₀ K₁ P₁ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (hlam : 0 < lam) (hτell : τ ≤ ell) (hK₁ : 0 ≤ K₁) :
    (δ * τ / lam ^ 2) * (K₁ / ell + (lam / τ) * P₁ * K₀) ≤
      δ * (K₁ / lam ^ 2 + P₁ * K₀ / lam) := by
  have hell : 0 < ell := hτ.trans_le hτell
  have heq : (δ * τ / lam ^ 2) * (K₁ / ell + (lam / τ) * P₁ * K₀) =
      δ * ((τ / ell) * (K₁ / lam ^ 2) + P₁ * K₀ / lam) := by
    field_simp
  rw [heq]
  apply mul_le_mul_of_nonneg_left _ hδ
  apply add_le_add _ le_rfl
  exact mul_le_of_le_one_left (div_nonneg hK₁ (sq_nonneg _)) ((div_le_one hell).mpr hτell)

/-- The first spatial derivative has original size δ, i.e. t^10 in (8.2). -/
theorem norm_fderiv_actualProbeCosColumn_slow_scale {ψ : E → ℝ} {A : E → F}
    (x : E) (hψ : DifferentiableAt ℝ ψ x) (hA : DifferentiableAt ℝ A x)
    (δ τ ell lam K₀ K₁ P₁ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (hlam : 0 < lam) (hτell : τ ≤ ell) (hK₁ : 0 ≤ K₁) (hP₁ : 0 ≤ P₁)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁) :
    ‖fderiv ℝ (actualProbeCosColumn δ τ lam ψ A) x‖ ≤
      δ * (K₁ / lam ^ 2 + P₁ * K₀ / lam) := by
  have h := norm_fderiv_actualProbeCosColumn_le x hψ hA δ τ lam
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _)),
    abs_of_pos (div_pos hlam hτ)] at h
  apply h.trans
  apply le_trans _ (probe_first_scale_inequality δ τ ell lam K₀ K₁ P₁ hδ hτ hlam hτell hK₁)
  gcongr

/-- The matching δ-scale first derivative for the sine parameter column. -/
theorem norm_fderiv_actualProbeSinColumn_slow_scale {ψ : E → ℝ} {A : E → F}
    (x : E) (hψ : DifferentiableAt ℝ ψ x) (hA : DifferentiableAt ℝ A x)
    (δ τ ell lam K₀ K₁ P₁ : ℝ) (hδ : 0 ≤ δ) (hτ : 0 < τ)
    (hlam : 0 < lam) (hτell : τ ≤ ell) (hK₁ : 0 ≤ K₁) (hP₁ : 0 ≤ P₁)
    (hA₀ : ‖A x‖ ≤ K₀) (hA₁ : ‖fderiv ℝ A x‖ ≤ K₁ / ell)
    (hψ₁ : ‖fderiv ℝ ψ x‖ ≤ P₁) :
    ‖fderiv ℝ (actualProbeSinColumn δ τ lam ψ A) x‖ ≤
      δ * (K₁ / lam ^ 2 + P₁ * K₀ / lam) := by
  have h := norm_fderiv_actualProbeSinColumn_le x hψ hA δ τ lam
  rw [abs_of_nonneg (div_nonneg (mul_nonneg hδ hτ.le) (sq_nonneg _)),
    abs_of_pos (div_pos hlam hτ)] at h
  apply h.trans
  apply le_trans _ (probe_first_scale_inequality δ τ ell lam K₀ K₁ P₁ hδ hτ hlam hτell hK₁)
  gcongr

#print axioms norm_fderiv_actualProbeCosColumn_slow_scale
#print axioms norm_fderiv_actualProbeSinColumn_slow_scale
end GlobalEmbedding.Offline
