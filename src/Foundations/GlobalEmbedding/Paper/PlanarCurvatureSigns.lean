import Mathlib.Analysis.Calculus.LocalExtr.Rolle
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Shift
import Mathlib.Algebra.Field.Periodic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

/-!
# Curvature of actual reflected unit-speed periodic planar profiles

Source: `main.tex`, `lem:planar`, lines 245–265.
DAG: `planar-curvature-signs`. The root-approved reflection argument avoids
the sphere angle-lift prerequisite while retaining both strict curvature signs.
All derivatives below are derivatives of the actual input coordinate functions.
-/

namespace GlobalEmbedding.Paper

/-- The determinant of the actual velocity and acceleration. -/
noncomputable def planarSignedCurvature (f g : ℝ → ℝ) (t : ℝ) : ℝ :=
  deriv f t * deriv (deriv g) t - deriv g t * deriv (deriv f) t

/-- Differentiating actual unit speed gives the true perpendicular acceleration,
and the determinant identifies its quarter-turn coefficient. -/
theorem planar_acceleration_eq_curvature
    {f g : ℝ → ℝ} (hf : Differentiable ℝ (deriv f))
    (hg : Differentiable ℝ (deriv g))
    (hunit : ∀ t, deriv f t ^ 2 + deriv g t ^ 2 = 1) (t : ℝ) :
    deriv (deriv f) t = -planarSignedCurvature f g t * deriv g t ∧
      deriv (deriv g) t = planarSignedCurvature f g t * deriv f t := by
  have hconst : (fun x ↦ deriv f x ^ 2 + deriv g x ^ 2) = fun _ ↦ (1 : ℝ) :=
    funext hunit
  have hd := (((hf t).hasDerivAt.pow 2).add ((hg t).hasDerivAt.pow 2)).deriv
  change deriv (fun x ↦ deriv f x ^ 2 + deriv g x ^ 2) t = _ at hd
  rw [hconst, deriv_const] at hd
  norm_num at hd
  have horth : deriv f t * deriv (deriv f) t +
      deriv g t * deriv (deriv g) t = 0 := by linarith
  have hu := hunit t
  constructor
  · dsimp only [planarSignedCurvature]
    nlinarith [congrArg (fun x : ℝ ↦ x * deriv (deriv f) t) hu,
      congrArg (fun x : ℝ ↦ x * deriv f t) horth]
  · dsimp only [planarSignedCurvature]
    nlinarith [congrArg (fun x : ℝ ↦ x * deriv (deriv g) t) hu,
      congrArg (fun x : ℝ ↦ x * deriv g t) horth]

/-- Translation invariance of the actual function differentiates to invariance
of its actual derivative, without any differentiability side assumption. -/
theorem deriv_half_period_even {f : ℝ → ℝ}
    (hf : ∀ t, f (t + 1 / 2) = f t) :
    ∀ t, deriv f (t + 1 / 2) = deriv f t := by
  intro t
  have he : (fun x ↦ f (x + 1 / 2)) = f := funext hf
  have hd := congrArg (fun F : ℝ → ℝ ↦ deriv F t) he
  simpa only [deriv_comp_add_const] using hd

/-- Actual half-period oddness differentiates to actual half-period oddness. -/
theorem deriv_half_period_odd {g : ℝ → ℝ}
    (hg : ∀ t, g (t + 1 / 2) = -g t) :
    ∀ t, deriv g (t + 1 / 2) = -deriv g t := by
  intro t
  have he : (fun x ↦ g (x + 1 / 2)) = fun x ↦ -g x := funext hg
  have hd := congrArg (fun F : ℝ → ℝ ↦ deriv F t) he
  simpa only [deriv_comp_add_const, deriv.fun_neg] using hd

/-- The reflection law of the actual planar map forces its actual signed
curvature to be odd under the half-period action. -/
theorem planar_curvature_half_period_odd {f g : ℝ → ℝ}
    (hf : ∀ t, f (t + 1 / 2) = f t)
    (hg : ∀ t, g (t + 1 / 2) = -g t) (t : ℝ) :
    planarSignedCurvature f g (t + 1 / 2) = -planarSignedCurvature f g t := by
  dsimp only [planarSignedCurvature]
  rw [deriv_half_period_even hf t, deriv_half_period_odd hg t,
    deriv_half_period_even (deriv_half_period_even hf) t,
    deriv_half_period_odd (deriv_half_period_odd hg) t]
  ring

/-- A genuine closed twice differentiable unit-speed planar profile cannot have
identically zero curvature. Zero curvature would make both actual first
derivatives constant; periodic Rolle makes both constants zero. -/
theorem planar_curvature_not_identically_zero
    {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdf : Differentiable ℝ (deriv f)) (hdg : Differentiable ℝ (deriv g))
    (hfp : Function.Periodic f 1) (hgp : Function.Periodic g 1)
    (hunit : ∀ t, deriv f t ^ 2 + deriv g t ^ 2 = 1) :
    ∃ t, planarSignedCurvature f g t ≠ 0 := by
  by_contra! hall
  have hzero (t : ℝ) : deriv (deriv f) t = 0 ∧ deriv (deriv g) t = 0 := by
    simpa only [hall t, neg_zero, zero_mul] using
      planar_acceleration_eq_curvature hdf hdg hunit t
  obtain ⟨x, _, hx⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    hf.continuous.continuousOn (by simpa only [zero_add] using (hfp 0).symm)
  obtain ⟨y, _, hy⟩ := exists_deriv_eq_zero (show (0 : ℝ) < 1 by norm_num)
    hg.continuous.continuousOn (by simpa only [zero_add] using (hgp 0).symm)
  have hfx : deriv f 0 = 0 :=
    (is_const_of_deriv_eq_zero hdf (fun t ↦ (hzero t).1) 0 x).trans hx
  have hgy : deriv g 0 = 0 :=
    (is_const_of_deriv_eq_zero hdg (fun t ↦ (hzero t).2) 0 y).trans hy
  have hu := hunit 0
  rw [hfx, hgy] at hu
  norm_num at hu

/-- The original both-sign conclusion for each actual period-one Hopf orbit.
Only genuine unit speed, periodicity and reflection of the input map are used;
no curvature-sign premise or angle lift is supplied. -/
theorem planar_curvature_both_signs
    {f g : ℝ → ℝ} (hf : Differentiable ℝ f) (hg : Differentiable ℝ g)
    (hdf : Differentiable ℝ (deriv f)) (hdg : Differentiable ℝ (deriv g))
    (hfp : Function.Periodic f 1) (hgp : Function.Periodic g 1)
    (hunit : ∀ t, deriv f t ^ 2 + deriv g t ^ 2 = 1)
    (hfreflect : ∀ t, f (t + 1 / 2) = f t)
    (hgreflect : ∀ t, g (t + 1 / 2) = -g t) :
    (∃ t, 0 < planarSignedCurvature f g t) ∧
      (∃ t, planarSignedCurvature f g t < 0) := by
  obtain ⟨t, ht⟩ := planar_curvature_not_identically_zero hf hg hdf hdg hfp hgp hunit
  have hodd := planar_curvature_half_period_odd hfreflect hgreflect t
  rcases lt_or_gt_of_ne ht with hneg | hpos
  · exact ⟨⟨t + 1 / 2, by linarith⟩, ⟨t, hneg⟩⟩
  · exact ⟨⟨t, hpos⟩, ⟨t + 1 / 2, by linarith⟩⟩

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.planar_acceleration_eq_curvature
#print axioms GlobalEmbedding.Paper.planar_curvature_half_period_odd
#print axioms GlobalEmbedding.Paper.planar_curvature_not_identically_zero
#print axioms GlobalEmbedding.Paper.planar_curvature_both_signs
