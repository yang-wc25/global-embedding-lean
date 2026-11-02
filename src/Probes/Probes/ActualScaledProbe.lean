import Probes.ActualOscillatoryRemainder
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Normed.Operator.NormedSpace

/-!
# The actual weighted probe columns and their original second-form scale

Source: (8.3). The real displacement columns are
`-δ τ lam⁻² cos(lam ψ / τ) A` and `-δ τ lam⁻² sin(lam ψ / τ) A`,
with `A = χ ν`. Their native spatial Hessians have the original principal
coefficient `δ / τ`, and the actual slow remainders are displayed and bounded.
-/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

-- Pin the standard nested operator instances, as in the existing rank-one
-- dictionary modules. These are the native operator norms, not new norms.
private noncomputable local instance probeBilinearSemi :
    SeminormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toSeminormedAddCommGroup
private noncomputable local instance probeBilinearNormed :
    NormedAddCommGroup (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedAddCommGroup
private noncomputable local instance probeBilinearNormedSpace :
    NormedSpace ℝ (E →L[ℝ] E →L[ℝ] F) :=
  ContinuousLinearMap.toNormedSpace

/-- The source's weighted fast phase, written in scalar-multiplication order. -/
def probeFastPhase (τ lam : ℝ) (ψ : E → ℝ) (x : E) : ℝ := (lam / τ) * ψ x

/-- Equality with the exact phase displayed in (8.1). -/
theorem probeFastPhase_eq (τ lam : ℝ) (ψ : E → ℝ) (x : E) :
    probeFastPhase τ lam ψ x = lam * ψ x / τ := by
  simp only [probeFastPhase, div_eq_mul_inv]
  ring

/-- Literal cosine displacement in (8.3). The cutoff and normal are in `A`. -/
def actualProbeCosColumn (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) : F :=
  (-(δ * τ / lam ^ 2)) • (Real.cos (probeFastPhase τ lam ψ x) • A x)

/-- Literal sine displacement from the same complex homogeneous amplitude. -/
def actualProbeSinColumn (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) : F :=
  (-(δ * τ / lam ^ 2)) • (Real.sin (probeFastPhase τ lam ψ x) • A x)

/-- Native spatial Hessian commutes with a constant scalar. -/
theorem fderiv_fderiv_const_smul_eq {A : E → F} (hA : ContDiff ℝ 2 A)
    (c : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ c • A y)) x = c • fderiv ℝ (fderiv ℝ A) x := by
  have hdA := hA.differentiable (by norm_num)
  have hDA := (hA.fderiv_right (m := 1) (by norm_num)).differentiable (by norm_num)
  have heq : fderiv ℝ (fun y ↦ c • A y) = fun y ↦ c • fderiv ℝ A y := by
    funext y
    exact fderiv_fun_const_smul (hdA y) c
  rw [heq, fderiv_fun_const_smul (hDA x) c]

/-- The fast phase's actual derivative is computed, including its true scale. -/
theorem fderiv_probeFastPhase {ψ : E → ℝ} (hψ : DifferentiableAt ℝ ψ x)
    (τ lam : ℝ) :
    fderiv ℝ (probeFastPhase τ lam ψ) x = (lam / τ) • fderiv ℝ ψ x := by
  exact fderiv_fun_const_smul hψ (lam / τ)

/-- Both derivatives of the phase are actual derivatives of the same function. -/
theorem fderiv_fderiv_probeFastPhase {ψ : E → ℝ} (hψ : ContDiff ℝ 2 ψ)
    (τ lam : ℝ) (x : E) :
    fderiv ℝ (fderiv ℝ (probeFastPhase τ lam ψ)) x =
      (lam / τ) • fderiv ℝ (fderiv ℝ ψ) x :=
  fderiv_fderiv_const_smul_eq hψ (lam / τ) x

/-- The literal phase rank-one tensor has the squared fast factor. -/
theorem phaseRankOneHessian_probeFastPhase {ψ : E → ℝ}
    (hψ : DifferentiableAt ℝ ψ x) (τ lam : ℝ) (A : E → F) :
    phaseRankOneHessian (probeFastPhase τ lam ψ) A x =
      (lam / τ) ^ 2 • phaseRankOneHessian ψ A x := by
  ext v w
  simp only [phaseRankOneHessian, fderiv_probeFastPhase hψ,
    ContinuousLinearMap.smulRight_apply, smul_apply, smul_eq_mul]
  module

/-- The original scaling identity producing `σ = δ / τ`. Both nonzero
hypotheses are essential here, and both follow from the source's positivity. -/
theorem probe_principal_scale (δ τ lam : ℝ) (hτ : τ ≠ 0) (hlam : lam ≠ 0) :
    (δ * τ / lam ^ 2) * (lam / τ) ^ 2 = δ / τ := by
  field_simp

/-- The actual cosine slow remainder, with the precise original amplitude. -/
def actualProbeCosRemainder (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) :
    E →L[ℝ] E →L[ℝ] F :=
  (-(δ * τ / lam ^ 2)) • actualCosSlowHessian (probeFastPhase τ lam ψ) A x

/-- The sine slow remainder carries exactly the same amplitude. -/
def actualProbeSinRemainder (δ τ lam : ℝ) (ψ : E → ℝ) (A : E → F) (x : E) :
    E →L[ℝ] E →L[ℝ] F :=
  (-(δ * τ / lam ^ 2)) • actualSinSlowHessian (probeFastPhase τ lam ψ) A x

/-- The actual weighted cosine column has principal Hessian `σ A dψ² cos`
with `σ = δ/τ`, plus its native slow remainder. -/
theorem actualProbeCosColumn_hessian {ψ : E → ℝ} {A : E → F}
    (hψ : ContDiff ℝ 2 ψ) (hA : ContDiff ℝ 2 A)
    (δ τ lam : ℝ) (hτ : τ ≠ 0) (hlam : lam ≠ 0) (x : E) :
    fderiv ℝ (fderiv ℝ (actualProbeCosColumn δ τ lam ψ A)) x =
      ((δ / τ) * Real.cos (lam * ψ x / τ)) • phaseRankOneHessian ψ A x +
      actualProbeCosRemainder δ τ lam ψ A x := by
  have hθ : ContDiff ℝ 2 (probeFastPhase τ lam ψ) := hψ.const_smul (lam / τ)
  change fderiv ℝ (fderiv ℝ (fun y ↦ (-(δ * τ / lam ^ 2)) •
    (Real.cos (probeFastPhase τ lam ψ y) • A y))) x = _
  have hmod : ContDiff ℝ 2 (fun y ↦ Real.cos (probeFastPhase τ lam ψ y) • A y) :=
    hθ.cos.smul hA
  rw [fderiv_fderiv_const_smul_eq hmod]
  unfold actualProbeCosRemainder actualCosSlowHessian
  rw [phaseRankOneHessian_probeFastPhase (hψ.differentiable (by norm_num) x)]
  rw [probeFastPhase_eq]
  rw [← probe_principal_scale δ τ lam hτ hlam]
  module

/-- The paired sine column has the same original second-form scale. -/
theorem actualProbeSinColumn_hessian {ψ : E → ℝ} {A : E → F}
    (hψ : ContDiff ℝ 2 ψ) (hA : ContDiff ℝ 2 A)
    (δ τ lam : ℝ) (hτ : τ ≠ 0) (hlam : lam ≠ 0) (x : E) :
    fderiv ℝ (fderiv ℝ (actualProbeSinColumn δ τ lam ψ A)) x =
      ((δ / τ) * Real.sin (lam * ψ x / τ)) • phaseRankOneHessian ψ A x +
      actualProbeSinRemainder δ τ lam ψ A x := by
  have hθ : ContDiff ℝ 2 (probeFastPhase τ lam ψ) := hψ.const_smul (lam / τ)
  change fderiv ℝ (fderiv ℝ (fun y ↦ (-(δ * τ / lam ^ 2)) •
    (Real.sin (probeFastPhase τ lam ψ y) • A y))) x = _
  have hmod : ContDiff ℝ 2 (fun y ↦ Real.sin (probeFastPhase τ lam ψ y) • A y) :=
    hθ.sin.smul hA
  rw [fderiv_fderiv_const_smul_eq hmod]
  unfold actualProbeSinRemainder actualSinSlowHessian
  rw [phaseRankOneHessian_probeFastPhase (hψ.differentiable (by norm_num) x)]
  rw [probeFastPhase_eq]
  rw [← probe_principal_scale δ τ lam hτ hlam]
  module

/-- A fully explicit bound for the actual cosine remainder at every point. -/
theorem norm_actualProbeCosRemainder_le {ψ : E → ℝ} {A : E → F}
    (hψ : ContDiff ℝ 2 ψ) (hA : ContDiff ℝ 2 A)
    (δ τ lam : ℝ) (x : E) :
    ‖actualProbeCosRemainder δ τ lam ψ A x‖ ≤ |δ * τ / lam ^ 2| *
      (‖fderiv ℝ (fderiv ℝ A) x‖ +
       2 * |lam / τ| * ‖fderiv ℝ ψ x‖ * ‖fderiv ℝ A x‖ +
       |lam / τ| * ‖fderiv ℝ (fderiv ℝ ψ) x‖ * ‖A x‖) := by
  have hθ : ContDiff ℝ 2 (probeFastPhase τ lam ψ) := hψ.const_smul (lam / τ)
  have h := norm_actualCosSlowHessian_le hθ hA x
  rw [fderiv_probeFastPhase (hψ.differentiable (by norm_num) x),
    fderiv_fderiv_probeFastPhase hψ] at h
  simp only [norm_smul, Real.norm_eq_abs] at h
  unfold actualProbeCosRemainder
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  convert h using 1 <;> ring

/-- The sine remainder obeys the identical bound, uniformly in fast angles. -/
theorem norm_actualProbeSinRemainder_le {ψ : E → ℝ} {A : E → F}
    (hψ : ContDiff ℝ 2 ψ) (hA : ContDiff ℝ 2 A)
    (δ τ lam : ℝ) (x : E) :
    ‖actualProbeSinRemainder δ τ lam ψ A x‖ ≤ |δ * τ / lam ^ 2| *
      (‖fderiv ℝ (fderiv ℝ A) x‖ +
       2 * |lam / τ| * ‖fderiv ℝ ψ x‖ * ‖fderiv ℝ A x‖ +
       |lam / τ| * ‖fderiv ℝ (fderiv ℝ ψ) x‖ * ‖A x‖) := by
  have hθ : ContDiff ℝ 2 (probeFastPhase τ lam ψ) := hψ.const_smul (lam / τ)
  have h := norm_actualSinSlowHessian_le hθ hA x
  rw [fderiv_probeFastPhase (hψ.differentiable (by norm_num) x),
    fderiv_fderiv_probeFastPhase hψ] at h
  simp only [norm_smul, Real.norm_eq_abs] at h
  unfold actualProbeSinRemainder
  rw [norm_smul, Real.norm_eq_abs, abs_neg]
  apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
  convert h using 1 <;> ring

#print axioms actualProbeCosColumn_hessian
#print axioms actualProbeSinColumn_hessian
#print axioms norm_actualProbeCosRemainder_le
#print axioms norm_actualProbeSinRemainder_le

end GlobalEmbedding.Offline
