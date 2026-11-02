import GlobalEmbedding.Offline.MomentCoefficients
import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
import Mathlib.Analysis.Calculus.BumpFunction.Normed
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.Analysis.Calculus.ContDiff.WithLp
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

/-!
# Smooth compactly supported kernels with finitely many zero moments

Source: `literature/parallelizable-stable-plus-one/main.tex`, proof of
`thm:repair`, lines 700–702, and `dag/nodes/repair-moment-kernel.json`.

The construction is the finite signed combination of normalized positive
dilations specified by the paper. The scalar weights are the explicit
Lagrange coefficients in `MomentCoefficients`. Haar change of variables
proves the moment identities. No positivity of the resulting kernel is
asserted or used.

This file is an isolated candidate, not a shared-library landing or an
acceptance claim for the full repair theorem.
-/

open MeasureTheory MeasureTheory.Measure
open scoped BigOperators ContDiff

namespace GlobalEmbedding.Offline

noncomputable section

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Mass-preserving dilation by the positive factor `c`; the Jacobian
normalization uses the actual real dimension of the source space. -/
def scaledMomentKernel (c : ℝ) (kappa : E → ℝ) (x : E) : ℝ :=
  (c ^ Module.finrank ℝ E)⁻¹ * kappa (c⁻¹ • x)

/-- A finite signed combination of positive dilations, with the explicit
nodes and Lagrange weights from `MomentCoefficients`. -/
def finiteMomentKernel (r : ℕ) (kappa : E → ℝ) (x : E) : ℝ :=
  ∑ i : Fin (r + 1), momentCoefficient (momentDilation r) i *
    scaledMomentKernel (momentDilation r i) kappa x

/-- Dilation and multiplication by a fixed scalar preserve smoothness. -/
theorem scaledMomentKernel_contDiff {kappa : E → ℝ}
    (h : ContDiff ℝ ∞ kappa) (c : ℝ) :
    ContDiff ℝ ∞ (scaledMomentKernel c kappa) := by
  exact contDiff_const.mul (h.comp (contDiff_const.smul contDiff_id))

/-- Nonzero dilation preserves compact support. -/
theorem scaledMomentKernel_hasCompactSupport {kappa : E → ℝ}
    (h : HasCompactSupport kappa) {c : ℝ} (hc : c ≠ 0) :
    HasCompactSupport (scaledMomentKernel c kappa) :=
  (h.comp_smul (inv_ne_zero hc)).mul_left

/-- The finite signed sum is smooth whenever the original bump is smooth. -/
theorem finiteMomentKernel_contDiff {kappa : E → ℝ}
    (h : ContDiff ℝ ∞ kappa) (r : ℕ) :
    ContDiff ℝ ∞ (finiteMomentKernel r kappa) := by
  exact ContDiff.sum fun i _ =>
    contDiff_const.mul (scaledMomentKernel_contDiff h (momentDilation r i))

/-- The finite signed sum is compactly supported. -/
theorem finiteMomentKernel_hasCompactSupport {kappa : E → ℝ}
    (h : HasCompactSupport kappa) (r : ℕ) :
    HasCompactSupport (finiteMomentKernel r kappa) := by
  have hterm : ∀ i : Fin (r + 1), HasCompactSupport
      (fun x : E => momentCoefficient (momentDilation r) i *
        scaledMomentKernel (momentDilation r i) kappa x) := by
    intro i
    exact (scaledMomentKernel_hasCompactSupport h (momentDilation_pos r i).ne').mul_left
  have hsum := HasCompactSupport.finset_sum (s := Finset.univ)
    (f := fun i x => momentCoefficient (momentDilation r) i *
      scaledMomentKernel (momentDilation r i) kappa x) (fun i _ => hterm i)
  have heq : (∑ i : Fin (r + 1), fun x : E =>
      momentCoefficient (momentDilation r) i *
        scaledMomentKernel (momentDilation r i) kappa x) = finiteMomentKernel r kappa := by
    funext x
    simp only [Finset.sum_apply, finiteMomentKernel]
  rwa [heq] at hsum

/-- If the original bump vanishes outside radius `rho`, so does every
positive dilation of scale at most one. -/
theorem scaledMomentKernel_zero_of_norm_ge {kappa : E → ℝ} {rho c : ℝ}
    (hc : 0 < c) (hc1 : c ≤ 1)
    (hzero : ∀ x, rho ≤ ‖x‖ → kappa x = 0)
    (x : E) (hx : rho ≤ ‖x‖) : scaledMomentKernel c kappa x = 0 := by
  have hnorm : ‖c⁻¹ • x‖ = ‖x‖ / c := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hc), div_eq_mul_inv,
      mul_comm]
  have hbound : ‖x‖ ≤ ‖x‖ / c := by
    apply (le_div_iff₀ hc).2
    exact mul_le_of_le_one_right (norm_nonneg x) hc1
  simp only [scaledMomentKernel, hzero _ (hx.trans (hbound.trans_eq hnorm.symm)),
    mul_zero]

/-- The topological support of the signed sum stays inside the same closed
ball. The proof uses the pointwise vanishing of every summand and closure. -/
theorem finiteMomentKernel_tsupport_subset {kappa : E → ℝ} {rho : ℝ}
    (hzero : ∀ x, rho ≤ ‖x‖ → kappa x = 0) (r : ℕ) :
    tsupport (finiteMomentKernel r kappa) ⊆ Metric.closedBall (0 : E) rho := by
  apply closure_minimal _ Metric.isClosed_closedBall
  intro x hx
  rw [Metric.mem_closedBall, dist_zero_right]
  by_contra hxball
  have hzeroK : finiteMomentKernel r kappa x = 0 := by
    apply Finset.sum_eq_zero
    intro i hi
    rw [scaledMomentKernel_zero_of_norm_ge (momentDilation_pos r i)
      (momentDilation_lt_one r i).le hzero x (le_of_lt (lt_of_not_ge hxball)), mul_zero]
  exact hx hzeroK

section Integral

variable [MeasurableSpace E] [BorelSpace E] [FiniteDimensional ℝ E]
    (mu : Measure E) [IsAddHaarMeasure mu]

/-- The Jacobian in `scaledMomentKernel` exactly preserves the integral,
including the zero-dimensional case. -/
theorem scaledMomentKernel_integral (kappa : E → ℝ) {c : ℝ} (hc : 0 < c) :
    (∫ x, scaledMomentKernel c kappa x ∂mu) = ∫ x, kappa x ∂mu := by
  simp only [scaledMomentKernel]
  rw [integral_const_mul, Measure.integral_comp_inv_smul_of_nonneg mu kappa hc.le]
  simp only [smul_eq_mul, ← mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ hc.ne'), one_mul]

/-- Homogeneous moments transform by their actual degree under normalized
dilation. The identity is proved by change of variables, not postulated as
a property of the kernel. -/
theorem scaledMomentKernel_homogeneous_integral (kappa P : E → ℝ) {c : ℝ}
    (hc : 0 < c) (k : ℕ) (hP : ∀ a x, P (a • x) = a ^ k * P x) :
    (∫ x, P x * scaledMomentKernel c kappa x ∂mu) =
      c ^ k * ∫ x, P x * kappa x ∂mu := by
  have hscale : ∀ x, P x = c ^ k * P (c⁻¹ • x) := by
    intro x
    simpa only [smul_smul, mul_inv_cancel₀ hc.ne', one_smul] using hP c (c⁻¹ • x)
  calc
    (∫ x, P x * scaledMomentKernel c kappa x ∂mu) =
        ∫ x, (c ^ k * (c ^ Module.finrank ℝ E)⁻¹) *
          ((fun y => P y * kappa y) (c⁻¹ • x)) ∂mu := by
      apply integral_congr_ae
      filter_upwards [] with x
      rw [scaledMomentKernel, hscale x]
      ring
    _ = (c ^ k * (c ^ Module.finrank ℝ E)⁻¹) *
        ∫ x, ((fun y => P y * kappa y) (c⁻¹ • x)) ∂mu :=
      integral_const_mul _ _
    _ = c ^ k * ∫ x, P x * kappa x ∂mu := by
      rw [Measure.integral_comp_inv_smul_of_nonneg mu (fun y : E => P y * kappa y) hc.le]
      simp only [smul_eq_mul]
      field_simp [pow_ne_zero _ hc.ne']

/-- The finite-moment kernel has integral one whenever the original bump
does. Integrability of each summand follows from smoothness and compact
support before the finite sum is interchanged with the integral. -/
theorem finiteMomentKernel_integral {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (hmass : (∫ x, kappa x ∂mu) = 1) (r : ℕ) :
    (∫ x, finiteMomentKernel r kappa x ∂mu) = 1 := by
  unfold finiteMomentKernel
  rw [integral_finsetSum Finset.univ]
  · simp_rw [integral_const_mul,
      scaledMomentKernel_integral mu kappa (momentDilation_pos r _), hmass, mul_one]
    exact momentCoefficient_sum _ (momentDilation_injective r)
  · intro i hi
    exact ((scaledMomentKernel_contDiff hsmooth _).continuous.integrable_of_hasCompactSupport
      (scaledMomentKernel_hasCompactSupport hcompact (momentDilation_pos r i).ne')).const_mul _

/-- Every continuous homogeneous polynomial of positive degree at most `r`
has zero moment against the constructed kernel. The proof factors out its
original moment and applies the proved scalar Lagrange moment equation. -/
theorem finiteMomentKernel_homogeneous_moment {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (r : ℕ) (P : E → ℝ) (hPcont : Continuous P) {k : ℕ}
    (hk0 : 0 < k) (hkr : k ≤ r)
    (hP : ∀ a x, P (a • x) = a ^ k * P x) :
    (∫ x, P x * finiteMomentKernel r kappa x ∂mu) = 0 := by
  have hInt : ∀ i : Fin (r + 1), Integrable
      (fun x => momentCoefficient (momentDilation r) i *
        (P x * scaledMomentKernel (momentDilation r i) kappa x)) mu := by
    intro i
    apply Integrable.const_mul
    exact (hPcont.mul (scaledMomentKernel_contDiff hsmooth _).continuous).integrable_of_hasCompactSupport
      (scaledMomentKernel_hasCompactSupport hcompact (momentDilation_pos r i).ne').mul_left
  have hfun : (fun x => P x * finiteMomentKernel r kappa x) =
      fun x => ∑ i : Fin (r + 1), momentCoefficient (momentDilation r) i *
        (P x * scaledMomentKernel (momentDilation r i) kappa x) := by
    funext x
    simp only [finiteMomentKernel, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i hi
    ring
  rw [hfun, integral_finsetSum Finset.univ (fun i _ => hInt i)]
  simp_rw [integral_const_mul,
    scaledMomentKernel_homogeneous_integral mu kappa P (momentDilation_pos r _) k hP,
    ← mul_assoc]
  rw [← Finset.sum_mul, momentDilation_moments r hkr]
  simp [Nat.ne_of_gt hk0]

omit [FiniteDimensional ℝ E] in
/-- Every fixed derivative of the constructed smooth compact kernel has
finite L1 norm; there is no bound uniform in the chosen moment order. -/
theorem finiteMomentKernel_integrable_derivative {kappa : E → ℝ}
    (hsmooth : ContDiff ℝ ∞ kappa) (hcompact : HasCompactSupport kappa)
    (r j : ℕ) :
    Integrable (fun x => ‖iteratedFDeriv ℝ j (finiteMomentKernel r kappa) x‖) mu := by
  have hcont : Continuous (iteratedFDeriv ℝ j (finiteMomentKernel r kappa)) :=
    ContDiff.continuous_iteratedFDeriv (by simp) (finiteMomentKernel_contDiff hsmooth r)
  exact (hcont.integrable_of_hasCompactSupport
    ((finiteMomentKernel_hasCompactSupport hcompact r).iteratedFDeriv j)).norm

end Integral

end

end GlobalEmbedding.Offline
