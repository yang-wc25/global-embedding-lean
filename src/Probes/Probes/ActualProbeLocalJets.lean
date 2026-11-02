import Probes.ActualScaledProbe

/-!
# Actual probe Hessians on the original open coordinate chart

All local formulas use C2 germs at the evaluation point, so they apply to the
paper's phase and coefficient fields without any global smooth extension.
Definitions, fast phase, original scaling and remainder are exactly those of
`ActualScaledProbe`.
-/
noncomputable section
open Filter Set
open scoped ContDiff Topology
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

private noncomputable local instance localProbeBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance localProbeBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance localProbeBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

/-- Native constant-scalar Hessian rule for a C2 germ. -/
theorem fderiv_fderiv_const_smul_eq_at {A : E → F} {x : E}
    (hA : ContDiffAt ℝ 2 A x) (c : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y ↦ c • A y)) x = c • fderiv ℝ (fderiv ℝ A) x := by
  have hDA := (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : fderiv ℝ (fun y ↦ c • A y) =ᶠ[𝓝 x] (fun y ↦ c • fderiv ℝ A y) := by
    filter_upwards [hA.eventually (by norm_num)] with y hy
    exact fderiv_fun_const_smul (hy.differentiableAt (by norm_num)) c
  rw [heq.fderiv_eq, fderiv_fun_const_smul hDA c]

/-- Original weighted phase Hessian under only local assumptions. -/
theorem fderiv_fderiv_probeFastPhase_at {ψ : E → ℝ} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ x) (τ lam : ℝ) :
    fderiv ℝ (fderiv ℝ (probeFastPhase τ lam ψ)) x =
      (lam / τ) • fderiv ℝ (fderiv ℝ ψ) x :=
  fderiv_fderiv_const_smul_eq_at hψ (lam / τ)

/-- Local exact slow remainder decomposition for the cosine wave. -/
theorem actualCosSlowHessian_apply_at {θ : E → ℝ} {A : E → F} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (hA : ContDiffAt ℝ 2 A x) (v w : E) :
    actualCosSlowHessian θ A x v w =
      Real.cos (θ x) • fderiv ℝ (fderiv ℝ A) x v w -
      Real.sin (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) := by
  simp only [actualCosSlowHessian, phaseRankOneHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [fderiv_fderiv_cos_smul_apply_at hθ hA]
  module

/-- The local sine remainder retains the same actual phase and amplitude jets. -/
theorem actualSinSlowHessian_apply_at {θ : E → ℝ} {A : E → F} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (hA : ContDiffAt ℝ 2 A x) (v w : E) :
    actualSinSlowHessian θ A x v w =
      Real.sin (θ x) • fderiv ℝ (fderiv ℝ A) x v w +
      Real.cos (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) := by
  simp only [actualSinSlowHessian, phaseRankOneHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [fderiv_fderiv_sin_smul_apply_at hθ hA]
  module

/-- The exact native cosine remainder bound is local in the original chart. -/
theorem norm_actualCosSlowHessian_le_at {θ : E → ℝ} {A : E → F} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (hA : ContDiffAt ℝ 2 A x) :
    ‖actualCosSlowHessian θ A x‖ ≤
      ‖fderiv ℝ (fderiv ℝ A) x‖ +
      2 * ‖fderiv ℝ θ x‖ * ‖fderiv ℝ A x‖ +
      ‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [actualCosSlowHessian_apply_at hθ hA]
  calc
    _ ≤ ‖Real.cos (θ x) • fderiv ℝ (fderiv ℝ A) x v w‖ +
        ‖Real.sin (θ x) • ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x)‖ := norm_sub_le _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ A) x v w‖ +
        ‖(fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _))
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _))
    _ ≤ ‖fderiv ℝ (fderiv ℝ A) x‖ * ‖v‖ * ‖w‖ +
        (2 * ‖fderiv ℝ θ x‖ * ‖fderiv ℝ A x‖ +
          ‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖A x‖) * ‖v‖ * ‖w‖ :=
      add_le_add ((fderiv ℝ (fderiv ℝ A) x).le_opNorm₂ v w)
        (norm_phase_amplitude_mixed_le θ A x v w)
    _ = _ := by ring

/-- The same local bound for the sine partner. -/
theorem norm_actualSinSlowHessian_le_at {θ : E → ℝ} {A : E → F} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (hA : ContDiffAt ℝ 2 A x) :
    ‖actualSinSlowHessian θ A x‖ ≤
      ‖fderiv ℝ (fderiv ℝ A) x‖ +
      2 * ‖fderiv ℝ θ x‖ * ‖fderiv ℝ A x‖ +
      ‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [actualSinSlowHessian_apply_at hθ hA]
  calc
    _ ≤ ‖Real.sin (θ x) • fderiv ℝ (fderiv ℝ A) x v w‖ +
        ‖Real.cos (θ x) • ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x)‖ := norm_add_le _ _
    _ ≤ ‖fderiv ℝ (fderiv ℝ A) x v w‖ +
        ‖(fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x‖ := by
      simp only [norm_smul, Real.norm_eq_abs]
      exact add_le_add
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_sin_le_one _))
        (mul_le_of_le_one_left (norm_nonneg _) (Real.abs_cos_le_one _))
    _ ≤ ‖fderiv ℝ (fderiv ℝ A) x‖ * ‖v‖ * ‖w‖ +
        (2 * ‖fderiv ℝ θ x‖ * ‖fderiv ℝ A x‖ +
          ‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖A x‖) * ‖v‖ * ‖w‖ :=
      add_le_add ((fderiv ℝ (fderiv ℝ A) x).le_opNorm₂ v w)
        (norm_phase_amplitude_mixed_le θ A x v w)
    _ = _ := by ring

/-- The original cosine principal Hessian and actual remainder, locally. -/
theorem actualProbeCosColumn_hessian_at {ψ : E → ℝ} {A : E → F} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x)
    (δ τ lam : ℝ) (hτ : τ ≠ 0) (hlam : lam ≠ 0) :
    fderiv ℝ (fderiv ℝ (actualProbeCosColumn δ τ lam ψ A)) x =
      ((δ / τ) * Real.cos (lam * ψ x / τ)) • phaseRankOneHessian ψ A x +
      actualProbeCosRemainder δ τ lam ψ A x := by
  have hθ : ContDiffAt ℝ 2 (probeFastPhase τ lam ψ) x := hψ.const_smul (lam / τ)
  have hmod : ContDiffAt ℝ 2 (fun y ↦ Real.cos (probeFastPhase τ lam ψ y) • A y) x :=
    hθ.cos.smul hA
  unfold actualProbeCosColumn
  rw [fderiv_fderiv_const_smul_eq_at hmod]
  unfold actualProbeCosRemainder actualCosSlowHessian
  rw [phaseRankOneHessian_probeFastPhase (hψ.differentiableAt (by norm_num)), probeFastPhase_eq,
    ← probe_principal_scale δ τ lam hτ hlam]
  module

/-- The matching original sine principal Hessian and retained remainder. -/
theorem actualProbeSinColumn_hessian_at {ψ : E → ℝ} {A : E → F} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x)
    (δ τ lam : ℝ) (hτ : τ ≠ 0) (hlam : lam ≠ 0) :
    fderiv ℝ (fderiv ℝ (actualProbeSinColumn δ τ lam ψ A)) x =
      ((δ / τ) * Real.sin (lam * ψ x / τ)) • phaseRankOneHessian ψ A x +
      actualProbeSinRemainder δ τ lam ψ A x := by
  have hθ : ContDiffAt ℝ 2 (probeFastPhase τ lam ψ) x := hψ.const_smul (lam / τ)
  have hmod : ContDiffAt ℝ 2 (fun y ↦ Real.sin (probeFastPhase τ lam ψ y) • A y) x :=
    hθ.sin.smul hA
  unfold actualProbeSinColumn
  rw [fderiv_fderiv_const_smul_eq_at hmod]
  unfold actualProbeSinRemainder actualSinSlowHessian
  rw [phaseRankOneHessian_probeFastPhase (hψ.differentiableAt (by norm_num)), probeFastPhase_eq,
    ← probe_principal_scale δ τ lam hτ hlam]
  module

/-- Explicit local cosine remainder norm bound in the same native operator norm. -/
theorem norm_actualProbeCosRemainder_le_at {ψ : E → ℝ} {A : E → F} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x) (δ τ lam : ℝ) :
    ‖actualProbeCosRemainder δ τ lam ψ A x‖ ≤ |δ * τ / lam ^ 2| *
      (‖fderiv ℝ (fderiv ℝ A) x‖ +
       2 * |lam / τ| * ‖fderiv ℝ ψ x‖ * ‖fderiv ℝ A x‖ +
       |lam / τ| * ‖fderiv ℝ (fderiv ℝ ψ) x‖ * ‖A x‖) := by
  have hθ : ContDiffAt ℝ 2 (probeFastPhase τ lam ψ) x := hψ.const_smul (lam / τ)
  have h := norm_actualCosSlowHessian_le_at hθ hA
  rw [fderiv_probeFastPhase (hψ.differentiableAt (by norm_num)),
    fderiv_fderiv_probeFastPhase_at hψ] at h
  simp only [norm_smul, Real.norm_eq_abs] at h
  unfold actualProbeCosRemainder
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  convert h using 1 <;> ring

/-- Explicit local sine remainder bound with exactly the same constant. -/
theorem norm_actualProbeSinRemainder_le_at {ψ : E → ℝ} {A : E → F} {x : E}
    (hψ : ContDiffAt ℝ 2 ψ x) (hA : ContDiffAt ℝ 2 A x) (δ τ lam : ℝ) :
    ‖actualProbeSinRemainder δ τ lam ψ A x‖ ≤ |δ * τ / lam ^ 2| *
      (‖fderiv ℝ (fderiv ℝ A) x‖ +
       2 * |lam / τ| * ‖fderiv ℝ ψ x‖ * ‖fderiv ℝ A x‖ +
       |lam / τ| * ‖fderiv ℝ (fderiv ℝ ψ) x‖ * ‖A x‖) := by
  have hθ : ContDiffAt ℝ 2 (probeFastPhase τ lam ψ) x := hψ.const_smul (lam / τ)
  have h := norm_actualSinSlowHessian_le_at hθ hA
  rw [fderiv_probeFastPhase (hψ.differentiableAt (by norm_num)),
    fderiv_fderiv_probeFastPhase_at hψ] at h
  simp only [norm_smul, Real.norm_eq_abs] at h
  unfold actualProbeSinRemainder
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  convert h using 1 <;> ring

#print axioms actualProbeCosColumn_hessian_at
#print axioms actualProbeSinColumn_hessian_at
#print axioms norm_actualProbeCosRemainder_le_at
#print axioms norm_actualProbeSinRemainder_le_at
end GlobalEmbedding.Offline
