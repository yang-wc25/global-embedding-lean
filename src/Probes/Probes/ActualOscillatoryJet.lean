import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Tactic.Module
import Mathlib.Tactic.Ring

/-!
# Actual second spatial jets of sine and cosine probe displacements

Source: `main.tex`, (8.1), (8.3), and the paragraph immediately following
(8.3). All derivatives in this file are native `fderiv` of the displayed
functions. Slow-amplitude and nonlinear-phase terms are retained explicitly.
No derivative identity or prescribed Hessian is supplied as an assumption.
-/

noncomputable section
open Filter
open scoped ContDiff Topology

namespace GlobalEmbedding.Offline

variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The actual product Hessian, in its original normed vector-space target.
This retains both mixed terms and the scalar Hessian term. -/
theorem fderiv_fderiv_smul_apply_at
    {c : E → ℝ} {A : E → F} {x : E} (hc : ContDiffAt ℝ 2 c x)
    (hA : ContDiffAt ℝ 2 A x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ c y • A y)) x v w =
      c x • fderiv ℝ (fderiv ℝ A) x v w +
      (fderiv ℝ c x v) • fderiv ℝ A x w +
      (fderiv ℝ c x w) • fderiv ℝ A x v +
      (fderiv ℝ (fderiv ℝ c) x v w) • A x := by
  have hdc : DifferentiableAt ℝ c x := hc.differentiableAt (by norm_num)
  have hdA : DifferentiableAt ℝ A x := hA.differentiableAt (by norm_num)
  have hDc : DifferentiableAt ℝ (fderiv ℝ c) x :=
    (hc.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDA : DifferentiableAt ℝ (fderiv ℝ A) x :=
    (hA.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDprod : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ c y • A y)) x :=
    ((hc.smul hA).fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y ↦ fderiv ℝ (fun z ↦ c z • A z) y w) =ᶠ[𝓝 x]
      (fun y ↦ c y • fderiv ℝ A y w + (fderiv ℝ c y w) • A y) := by
    filter_upwards [hc.eventually (by norm_num), hA.eventually (by norm_num)] with y hcy hAy
    rw [fderiv_fun_smul (hcy.differentiableAt (by norm_num)) (hAy.differentiableAt (by norm_num))]
    rfl
  have hleft := fderiv_clm_apply hDprod (differentiableAt_const w)
  have hright := ((hdc.hasFDerivAt.smul
      (hDA.hasFDerivAt.clm_apply (hasFDerivAt_const w x))).add
    ((hDc.hasFDerivAt.clm_apply (hasFDerivAt_const w x)).smul
      hdA.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y ↦ c y • fderiv ℝ A y w +
    (fderiv ℝ c y w) • A y) x = _ at hright
  rw [heq.fderiv_eq] at hleft
  rw [hright] at hleft
  have hev := congrArg (fun L : E →L[ℝ] F ↦ L v) hleft
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.flip_apply, zero_apply, map_zero,
    zero_add, add_zero, fderiv_const_apply] at hev
  simpa only [add_assoc] using hev.symm

/-- Global-C2 specialization of the local native product Hessian. -/
theorem fderiv_fderiv_smul_apply
    {c : E → ℝ} {A : E → F} (hc : ContDiff ℝ 2 c)
    (hA : ContDiff ℝ 2 A) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ c y • A y)) x v w =
      c x • fderiv ℝ (fderiv ℝ A) x v w +
      (fderiv ℝ c x v) • fderiv ℝ A x w +
      (fderiv ℝ c x w) • fderiv ℝ A x v +
      (fderiv ℝ (fderiv ℝ c) x v w) • A x :=
  fderiv_fderiv_smul_apply_at hc.contDiffAt hA.contDiffAt v w

/-- Native first derivative of a cosine coefficient times an actual vector
amplitude. This is the real part of the existing complex oscillatory first jet. -/
theorem fderiv_cos_smul_apply {θ : E → ℝ} {A : E → F}
    (hθ : DifferentiableAt ℝ θ x) (hA : DifferentiableAt ℝ A x) (w : E) :
    fderiv ℝ (fun y ↦ Real.cos (θ y) • A y) x w =
      Real.cos (θ x) • fderiv ℝ A x w -
        (Real.sin (θ x) * fderiv ℝ θ x w) • A x := by
  have hd := (hθ.hasFDerivAt.cos.smul hA.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ Real.cos (θ y) • A y) x = _ at hd
  rw [hd]
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.smulRight_apply, smul_eq_mul]
  module

/-- Native first derivative of the sine partner of the same actual wave. -/
theorem fderiv_sin_smul_apply {θ : E → ℝ} {A : E → F}
    (hθ : DifferentiableAt ℝ θ x) (hA : DifferentiableAt ℝ A x) (w : E) :
    fderiv ℝ (fun y ↦ Real.sin (θ y) • A y) x w =
      Real.sin (θ x) • fderiv ℝ A x w +
        (Real.cos (θ x) * fderiv ℝ θ x w) • A x := by
  have hd := (hθ.hasFDerivAt.sin.smul hA.hasFDerivAt).fderiv
  change fderiv ℝ (fun y ↦ Real.sin (θ y) • A y) x = _ at hd
  rw [hd]
  rfl

/-- The Hessian of the actual cosine of a nonlinear phase. In particular the
second derivative of the slow phase is not silently discarded. -/
theorem fderiv_fderiv_cos_apply_at {θ : E → ℝ} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (θ y))) x v w =
      -Real.cos (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w -
        Real.sin (θ x) * fderiv ℝ (fderiv ℝ θ) x v w := by
  have hdθ : DifferentiableAt ℝ θ x := hθ.differentiableAt (by norm_num)
  have hDθ : DifferentiableAt ℝ (fderiv ℝ θ) x :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDcos : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ Real.cos (θ y))) x :=
    (hθ.cos.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y ↦ fderiv ℝ (fun z ↦ Real.cos (θ z)) y w) =ᶠ[𝓝 x]
      (fun y ↦ -(Real.sin (θ y) * fderiv ℝ θ y w)) := by
    filter_upwards [hθ.eventually (by norm_num)] with y hy
    rw [(hy.differentiableAt (by norm_num)).hasFDerivAt.cos.fderiv]
    simp [smul_eq_mul]
  have hl := fderiv_clm_apply hDcos (differentiableAt_const w)
  rw [heq.fderiv_eq] at hl
  have hr := ((hdθ.hasFDerivAt.sin.mul
    (hDθ.hasFDerivAt.clm_apply (hasFDerivAt_const w x))).neg).fderiv
  change fderiv ℝ (fun y ↦ -(Real.sin (θ y) * fderiv ℝ θ y w)) x = _ at hr
  rw [hr] at hl
  have hev := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hl
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    neg_apply, map_zero, zero_add, add_zero,
    fderiv_const_apply, smul_eq_mul] at hev
  rw [← hev]
  ring

/-- The sine partner's actual nonlinear-phase Hessian. -/
theorem fderiv_fderiv_sin_apply_at {θ : E → ℝ} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.sin (θ y))) x v w =
      -Real.sin (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w +
        Real.cos (θ x) * fderiv ℝ (fderiv ℝ θ) x v w := by
  have hdθ : DifferentiableAt ℝ θ x := hθ.differentiableAt (by norm_num)
  have hDθ : DifferentiableAt ℝ (fderiv ℝ θ) x :=
    (hθ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hDsin : DifferentiableAt ℝ (fderiv ℝ (fun y ↦ Real.sin (θ y))) x :=
    (hθ.sin.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have heq : (fun y ↦ fderiv ℝ (fun z ↦ Real.sin (θ z)) y w) =ᶠ[𝓝 x]
      (fun y ↦ Real.cos (θ y) * fderiv ℝ θ y w) := by
    filter_upwards [hθ.eventually (by norm_num)] with y hy
    rw [(hy.differentiableAt (by norm_num)).hasFDerivAt.sin.fderiv]
    rfl
  have hl := fderiv_clm_apply hDsin (differentiableAt_const w)
  rw [heq.fderiv_eq] at hl
  have hr := (hdθ.hasFDerivAt.cos.mul
    (hDθ.hasFDerivAt.clm_apply (hasFDerivAt_const w x))).fderiv
  change fderiv ℝ (fun y ↦ Real.cos (θ y) * fderiv ℝ θ y w) x = _ at hr
  rw [hr] at hl
  have hev := congrArg (fun L : E →L[ℝ] ℝ ↦ L v) hl
  simp only [add_apply, ContinuousLinearMap.comp_apply,
    smul_apply, ContinuousLinearMap.smulRight_apply,
    ContinuousLinearMap.flip_apply, zero_apply,
    neg_apply, map_zero, zero_add, add_zero,
    fderiv_const_apply, smul_eq_mul] at hev
  rw [← hev]
  ring

/-- Global specialization of the local cosine phase Hessian. -/
theorem fderiv_fderiv_cos_apply {θ : E → ℝ} (hθ : ContDiff ℝ 2 θ)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (θ y))) x v w =
      -Real.cos (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w -
        Real.sin (θ x) * fderiv ℝ (fderiv ℝ θ) x v w :=
  fderiv_fderiv_cos_apply_at hθ.contDiffAt v w

/-- Global specialization of the local sine phase Hessian. -/
theorem fderiv_fderiv_sin_apply {θ : E → ℝ} (hθ : ContDiff ℝ 2 θ)
    (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.sin (θ y))) x v w =
      -Real.sin (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w +
        Real.cos (θ x) * fderiv ℝ (fderiv ℝ θ) x v w :=
  fderiv_fderiv_sin_apply_at hθ.contDiffAt v w

/-- The true cosine-amplitude Hessian, with both amplitude derivatives and
the nonlinear phase Hessian. The last term is the fast rank-one principal part. -/
theorem fderiv_fderiv_cos_smul_apply {θ : E → ℝ} {A : E → F}
    (hθ : ContDiff ℝ 2 θ) (hA : ContDiff ℝ 2 A) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (θ y) • A y)) x v w =
      Real.cos (θ x) • fderiv ℝ (fderiv ℝ A) x v w -
      Real.sin (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) -
      (Real.cos (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w) • A x := by
  rw [fderiv_fderiv_smul_apply hθ.cos hA,
    fderiv_fderiv_cos_apply hθ]
  rw [(hθ.differentiable (by norm_num) x).hasFDerivAt.cos.fderiv]
  simp only [smul_apply, smul_eq_mul]
  module

/-- The matching sine-amplitude Hessian, with the same principal sign and all
slow terms. This is the second parameter column of the original real wave. -/
theorem fderiv_fderiv_sin_smul_apply {θ : E → ℝ} {A : E → F}
    (hθ : ContDiff ℝ 2 θ) (hA : ContDiff ℝ 2 A) (x v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.sin (θ y) • A y)) x v w =
      Real.sin (θ x) • fderiv ℝ (fderiv ℝ A) x v w +
      Real.cos (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) -
      (Real.sin (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w) • A x := by
  rw [fderiv_fderiv_smul_apply hθ.sin hA,
    fderiv_fderiv_sin_apply hθ]
  rw [(hθ.differentiable (by norm_num) x).hasFDerivAt.sin.fderiv]
  simp only [smul_apply, smul_eq_mul]
  module

/-- Local-chart cosine-amplitude Hessian: C2 germs at the displayed point
suffice, with no global smooth extension assumption. -/
theorem fderiv_fderiv_cos_smul_apply_at {θ : E → ℝ} {A : E → F} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (hA : ContDiffAt ℝ 2 A x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.cos (θ y) • A y)) x v w =
      Real.cos (θ x) • fderiv ℝ (fderiv ℝ A) x v w -
      Real.sin (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) -
      (Real.cos (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w) • A x := by
  rw [fderiv_fderiv_smul_apply_at hθ.cos hA,
    fderiv_fderiv_cos_apply_at hθ]
  rw [(hθ.differentiableAt (by norm_num)).hasFDerivAt.cos.fderiv]
  simp only [smul_apply, smul_eq_mul]
  module

/-- The paired local-chart sine Hessian under the same C2 germ assumptions. -/
theorem fderiv_fderiv_sin_smul_apply_at {θ : E → ℝ} {A : E → F} {x : E}
    (hθ : ContDiffAt ℝ 2 θ x) (hA : ContDiffAt ℝ 2 A x) (v w : E) :
    fderiv ℝ (fderiv ℝ (fun y ↦ Real.sin (θ y) • A y)) x v w =
      Real.sin (θ x) • fderiv ℝ (fderiv ℝ A) x v w +
      Real.cos (θ x) •
        ((fderiv ℝ θ x v) • fderiv ℝ A x w +
         (fderiv ℝ θ x w) • fderiv ℝ A x v +
         (fderiv ℝ (fderiv ℝ θ) x v w) • A x) -
      (Real.sin (θ x) * fderiv ℝ θ x v * fderiv ℝ θ x w) • A x := by
  rw [fderiv_fderiv_smul_apply_at hθ.sin hA,
    fderiv_fderiv_sin_apply_at hθ]
  rw [(hθ.differentiableAt (by norm_num)).hasFDerivAt.sin.fderiv]
  simp only [smul_apply, smul_eq_mul]
  module

#print axioms fderiv_fderiv_smul_apply_at
#print axioms fderiv_fderiv_cos_smul_apply_at
#print axioms fderiv_fderiv_sin_smul_apply_at

end GlobalEmbedding.Offline
