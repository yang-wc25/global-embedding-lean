import Probes.ActualOscillatoryJet
import Mathlib.Tactic.GCongr

/-!
# Native operator-norm bounds for the actual oscillatory Hessian remainders

Source: the slow differentiation term following (8.3). The remainder is
literally the native Hessian minus its fast rank-one part, and the bound uses
native operator norms of the same amplitude and phase. Constants are explicit
and independent of the fast angle.
-/

noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The genuine rank-one Hessian tensor `dθ ⊗ dθ ⊗ A`. -/
def phaseRankOneHessian (θ : E → ℝ) (A : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  (fderiv ℝ θ x).smulRight ((fderiv ℝ θ x).smulRight (A x))

/-- The actual cosine Hessian with its negative fast part removed. -/
def actualCosSlowHessian (θ : E → ℝ) (A : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (θ y) • A y)) x +
    Real.cos (θ x) • phaseRankOneHessian θ A x

/-- The paired sine remainder, with the same fast tensor. -/
def actualSinSlowHessian (θ : E → ℝ) (A : E → F) (x : E) : E →L[ℝ] E →L[ℝ] F :=
  fderiv ℝ (fderiv ℝ (fun y ↦ Real.sin (θ y) • A y)) x +
    Real.sin (θ x) • phaseRankOneHessian θ A x

/-- The literal remainder consists only of amplitude second derivatives,
mixed slow/fast first derivatives, and the slow phase Hessian. -/
theorem actualCosSlowHessian_apply {θ : E → ℝ} {A : E → F}
    (hθ : ContDiff ℝ 2 θ) (hA : ContDiff ℝ 2 A) (x v w : E) :
    actualCosSlowHessian θ A x v w =
      Real.cos (θ x) • fderiv ℝ (fderiv ℝ A) x v w -
      Real.sin (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) := by
  simp only [actualCosSlowHessian, phaseRankOneHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [fderiv_fderiv_cos_smul_apply hθ hA]
  module

/-- The same exact decomposition for the sine partner. -/
theorem actualSinSlowHessian_apply {θ : E → ℝ} {A : E → F}
    (hθ : ContDiff ℝ 2 θ) (hA : ContDiff ℝ 2 A) (x v w : E) :
    actualSinSlowHessian θ A x v w =
      Real.sin (θ x) • fderiv ℝ (fderiv ℝ A) x v w +
      Real.cos (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) := by
  simp only [actualSinSlowHessian, phaseRankOneHessian, add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply]
  rw [fderiv_fderiv_sin_smul_apply hθ hA]
  module

/-- The native mixed slow terms have this bilinear bound; the factor two is
for the two actual product-rule terms, including different tangent vectors. -/
theorem norm_phase_amplitude_mixed_le (θ : E → ℝ) (A : E → F) (x v w : E) :
    ‖(fderiv ℝ θ x v) • fderiv ℝ A x w +
      (fderiv ℝ θ x w) • fderiv ℝ A x v +
      (fderiv ℝ (fderiv ℝ θ) x v w) • A x‖ ≤
    (2 * ‖fderiv ℝ θ x‖ * ‖fderiv ℝ A x‖ +
      ‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖A x‖) * ‖v‖ * ‖w‖ := by
  calc
    _ ≤ ‖(fderiv ℝ θ x v) • fderiv ℝ A x w‖ +
        ‖(fderiv ℝ θ x w) • fderiv ℝ A x v‖ +
        ‖(fderiv ℝ (fderiv ℝ θ) x v w) • A x‖ :=
      (norm_add_le _ _).trans (add_le_add (norm_add_le _ _) le_rfl)
    _ = ‖fderiv ℝ θ x v‖ * ‖fderiv ℝ A x w‖ +
        ‖fderiv ℝ θ x w‖ * ‖fderiv ℝ A x v‖ +
        ‖fderiv ℝ (fderiv ℝ θ) x v w‖ * ‖A x‖ := by simp only [norm_smul]
    _ ≤ (‖fderiv ℝ θ x‖ * ‖v‖) * (‖fderiv ℝ A x‖ * ‖w‖) +
        (‖fderiv ℝ θ x‖ * ‖w‖) * (‖fderiv ℝ A x‖ * ‖v‖) +
        (‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖v‖ * ‖w‖) * ‖A x‖ := by
      gcongr
      · exact (fderiv ℝ θ x).le_opNorm v
      · exact (fderiv ℝ A x).le_opNorm w
      · exact (fderiv ℝ θ x).le_opNorm w
      · exact (fderiv ℝ A x).le_opNorm v
      · exact (fderiv ℝ (fderiv ℝ θ) x).le_opNorm₂ v w
    _ = _ := by ring

/-- The cosine slow Hessian has a bound in the ORIGINAL operator norm.
The only numerical constant is two; in particular no phase-angle dependence
or atlas-cardinality factor enters. -/
theorem norm_actualCosSlowHessian_le {θ : E → ℝ} {A : E → F}
    (hθ : ContDiff ℝ 2 θ) (hA : ContDiff ℝ 2 A) (x : E) :
    ‖actualCosSlowHessian θ A x‖ ≤
      ‖fderiv ℝ (fderiv ℝ A) x‖ +
      2 * ‖fderiv ℝ θ x‖ * ‖fderiv ℝ A x‖ +
      ‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [actualCosSlowHessian_apply hθ hA]
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

/-- The sine partner has exactly the same uniform slow-derivative bound. -/
theorem norm_actualSinSlowHessian_le {θ : E → ℝ} {A : E → F}
    (hθ : ContDiff ℝ 2 θ) (hA : ContDiff ℝ 2 A) (x : E) :
    ‖actualSinSlowHessian θ A x‖ ≤
      ‖fderiv ℝ (fderiv ℝ A) x‖ +
      2 * ‖fderiv ℝ θ x‖ * ‖fderiv ℝ A x‖ +
      ‖fderiv ℝ (fderiv ℝ θ) x‖ * ‖A x‖ := by
  apply ContinuousLinearMap.opNorm_le_bound₂ _ (by positivity)
  intro v w
  rw [actualSinSlowHessian_apply hθ hA]
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

#print axioms actualCosSlowHessian_apply
#print axioms actualSinSlowHessian_apply
#print axioms norm_actualCosSlowHessian_le
#print axioms norm_actualSinSlowHessian_le

end GlobalEmbedding.Offline
