import GlobalEmbedding.Paper.CollarCauchyKovalevskayaAnalyticODE
import Mathlib.Analysis.Analytic.Binomial
import Mathlib.Analysis.Calculus.IteratedDeriv.FaaDiBruno
import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas

/-!
# An actual analytic Goursat majorant with nonnegative Taylor coefficients

Source: Gantumur, Math580 lecture notes2, Theorem18 proof, equations48–51.
-/

open scoped Topology NNReal ENNReal ContDiff
open Filter Set FormalMultilinearSeries

namespace GlobalEmbedding.Paper

/-- Extract a genuine analytic solution germ from the proved scalar ODE on a positive ball. -/
private theorem odeGermForMajorant {f : ℝ → ℝ} {y₀ : ℝ} (hf : AnalyticAt ℝ f y₀) :
    ∃ u : ℝ → ℝ, u 0 = y₀ ∧ AnalyticAt ℝ u 0 ∧
      ∀ᶠ t in 𝓝 0, HasDerivAt u (f (u t)) t := by
  obtain ⟨ε, hε, u, hu0, hua, hdu, _⟩ := collarCauchyKovalevskayaAnalyticODE hf
  exact ⟨u, hu0, hua 0 (Metric.mem_ball_self hε),
    eventually_of_mem (Metric.ball_mem_nhds 0 hε) hdu⟩

private theorem majorantDerivativeNonneg {f u : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hu : AnalyticAt ℝ u 0)
    (hu0 : u 0 = 0) (hdu : ∀ᶠ t in 𝓝 0, HasDerivAt u (f (u t)) t)
    (hfpos : ∀ n : ℕ, 0 ≤ iteratedDeriv n f 0) :
    ∀ n : ℕ, 0 ≤ iteratedDeriv n u 0 := by
  have hg : deriv u =ᶠ[𝓝 0] f ∘ u := hdu.mono fun t ht ↦ ht.deriv
  intro n
  induction n using Nat.strong_induction_on with
  | h k ih =>
    cases k with
    | zero => simpa only [iteratedDeriv_zero, hu0] using (le_refl (0 : ℝ))
    | succ n =>
      rw [iteratedDeriv_succ', (hg.iteratedDeriv n).self_of_nhds]
      have hf' : ContDiffAt ℝ ∞ f (u 0) := by simpa only [hu0] using hf.contDiffAt
      rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hf' hu.contDiffAt (by simp)]
      apply Finset.sum_nonneg
      intro c _
      apply mul_nonneg (by simpa only [hu0] using hfpos c.length)
      apply Finset.prod_nonneg
      intro j _
      exact ih (c.partSize j) (Nat.lt_succ_of_le (c.partSize_le j))

private theorem inverseAffineDerivativesNonneg (b c : ℝ) (hb : 0 < b) (hc : 0 ≤ c) :
    ∀ n : ℕ, 0 ≤ iteratedDeriv n (fun x : ℝ ↦ 1 / (b - c * x)) 0 := by
  let L : ℝ →L[ℝ] ℝ := c • ContinuousLinearMap.id ℝ ℝ
  let p : FormalMultilinearSeries ℝ ℝ ℝ :=
    .ofScalars ℝ (fun n ↦ (b ^ (n + 1))⁻¹)
  have hp : HasFPowerSeriesOnBall (fun x : ℝ ↦ 1 / (b - x)) p (L 0) ‖b‖ₑ := by
    simpa only [map_zero] using Real.one_div_sub_hasFPowerSeriesOnBall_zero hb.ne'
  have hcomp := hp.compContinuousLinearMap (u := L) (x := 0)
  intro n
  have hcoeff : (p.compContinuousLinearMap L).coeff n =
      c ^ n * (b ^ (n + 1))⁻¹ := by
    rw [FormalMultilinearSeries.coeff,
      FormalMultilinearSeries.compContinuousLinearMap_apply]
    simpa only [Function.comp_def, Pi.one_apply, L, _root_.smul_apply,
      ContinuousLinearMap.id_apply, smul_eq_mul, mul_one] using
      (show p n (fun _ ↦ c) = c ^ n * (b ^ (n + 1))⁻¹ by
        simp [p])
  have hfact := hcomp.factorial_smul (1 : ℝ) n
  have hformula : (n.factorial : ℝ) * (c ^ n * (b ^ (n + 1))⁻¹) =
      iteratedDeriv n (fun x : ℝ ↦ 1 / (b - c * x)) 0 := by
    simpa only [FormalMultilinearSeries.compContinuousLinearMap_apply,
      FormalMultilinearSeries.apply_eq_pow_smul_coeff,
      FormalMultilinearSeries.coeff_ofScalars, hcoeff, one_pow, one_mul,
      nsmul_eq_mul, smul_eq_mul, L, _root_.smul_apply,
      ContinuousLinearMap.id_apply, mul_one, Function.comp_def,
      ← iteratedDeriv_eq_iteratedFDeriv] using hfact
  rw [← hformula]
  positivity

private theorem quadraticInverseWithPositiveDerivatives (a b : ℝ) (ha : 0 ≤ a) (hb : 0 < b) :
    ∃ p : ℝ → ℝ, p 0 = 0 ∧ AnalyticAt ℝ p 0 ∧
      (∀ᶠ z in 𝓝 0, b * p z - a * (p z) ^ 2 = z) ∧
      ∀ n : ℕ, 0 ≤ iteratedDeriv n p 0 := by
  let f : ℝ → ℝ := fun x ↦ 1 / (b - (2 * a) * x)
  have hfa : AnalyticAt ℝ f 0 := by
    exact analyticAt_const.div (analyticAt_const.sub
      (analyticAt_const.mul analyticAt_id)) (by simpa using hb.ne')
  obtain ⟨p, hp0, hpa, hdp⟩ := odeGermForMajorant hfa
  have hpositive : ∀ n : ℕ, 0 ≤ iteratedDeriv n p 0 :=
    majorantDerivativeNonneg hfa hpa hp0 hdp
      (inverseAffineDerivativesNonneg b (2 * a) hb (mul_nonneg (by norm_num) ha))
  have hnz : ∀ᶠ t in 𝓝 0, b - (2 * a) * p t ≠ 0 := by
    have hc : ContinuousAt (fun t ↦ b - (2 * a) * p t) 0 :=
      continuousAt_const.sub (continuousAt_const.mul hpa.continuousAt)
    exact hc.eventually_ne (by simpa only [hp0, mul_zero, sub_zero] using hb.ne')
  have hderiv : ∀ᶠ t in 𝓝 0,
      HasDerivAt (fun z ↦ b * p z - a * (p z) ^ 2 - z) 0 t := by
    filter_upwards [hdp, hnz] with t ht hnt
    change HasDerivAt p (1 / (b - (2 * a) * p t)) t at ht
    convert ((ht.const_mul b).sub ((ht.pow 2).const_mul a)).sub (hasDerivAt_id t) using 1
    · ext z
      rfl
    · norm_num only [Nat.cast_ofNat, Nat.reduceSub, pow_one]
      field_simp [hnt]
      ring
  obtain ⟨ε, hε, hεderiv⟩ := Metric.eventually_nhds_iff_ball.mp hderiv
  have hidentity : ∀ t ∈ Metric.ball 0 ε, b * p t - a * (p t) ^ 2 - t = 0 := by
    intro t ht
    have hc := Metric.isOpen_ball.is_const_of_deriv_eq_zero
      (convex_ball (0 : ℝ) ε).isPreconnected
      (fun z hz ↦ (hεderiv z hz).differentiableAt.differentiableWithinAt)
      (fun z hz ↦ (hεderiv z hz).deriv) ht (Metric.mem_ball_self hε)
    simpa only [hp0, mul_zero, zero_pow (by omega : 2 ≠ 0), sub_self, sub_zero] using hc
  refine ⟨p, hp0, hpa, ?_, hpositive⟩
  filter_upwards [Metric.ball_mem_nhds 0 hε] with t ht
  exact sub_eq_zero.mp (hidentity t ht)

private theorem goursatBranchWithPositiveDerivatives (a b M R : ℝ) (ha : 0 ≤ a) (hb : 0 < b)
    (hM : 0 ≤ M) (hR : 0 < R) :
    ∃ g : ℝ → ℝ, g 0 = 0 ∧ AnalyticAt ℝ g 0 ∧
      (∀ᶠ S in 𝓝 0, b * g S - a * (g S) ^ 2 = M * S / (R - S)) ∧
      ∀ n : ℕ, 0 ≤ iteratedDeriv n g 0 := by
  obtain ⟨p, hp0, hpa, hPeq, hppos⟩ := quadraticInverseWithPositiveDerivatives a b ha hb
  let H : ℝ → ℝ := fun S ↦ -M + (M * R) * (1 / (R - S))
  have hHa : AnalyticAt ℝ H 0 := by
    exact analyticAt_const.add (analyticAt_const.mul
      (analyticAt_const.div (analyticAt_const.sub analyticAt_id) (by simpa using hR.ne')))
  have hH0 : H 0 = 0 := by simp [H, hR.ne', mul_assoc]
  have hHpos : ∀ n : ℕ, 0 ≤ iteratedDeriv n H 0 := by
    intro n
    cases n with
    | zero => simpa only [iteratedDeriv_zero, hH0] using (le_refl (0 : ℝ))
    | succ n =>
      change 0 ≤ iteratedDeriv (n + 1)
        (fun S : ℝ ↦ -M + (M * R) * (1 / (R - S))) 0
      rw [iteratedDeriv_const_add (Nat.succ_pos n), iteratedDeriv_const_mul_field]
      apply mul_nonneg (mul_nonneg hM hR.le)
      simpa only [one_mul] using inverseAffineDerivativesNonneg R 1 hR zero_le_one (n + 1)
  have hpa' : AnalyticAt ℝ p (H 0) := by simpa only [hH0] using hpa
  refine ⟨p ∘ H, by simp [hH0, hp0], hpa'.comp hHa, ?_, ?_⟩
  · have hHcont : Tendsto H (𝓝 0) (𝓝 0) := by
      have hc : Tendsto H (𝓝 0) (𝓝 (H 0)) := hHa.continuousAt
      rwa [hH0] at hc
    have hnz : ∀ᶠ S : ℝ in 𝓝 0, R - S ≠ 0 := by
      have hc : ContinuousAt (fun S : ℝ ↦ R - S) 0 := continuousAt_const.sub continuousAt_id
      exact hc.eventually_ne (by simpa only [sub_zero] using hR.ne')
    filter_upwards [hHcont.eventually hPeq, hnz] with S hP hS
    change b * p (H S) - a * (p (H S)) ^ 2 = _
    rw [hP]
    dsimp only [H]
    field_simp [hS]
    ring
  · intro n
    have hpCd : ContDiffAt ℝ ∞ p (H 0) := hpa'.contDiffAt
    rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hpCd hHa.contDiffAt (by simp)]
    apply Finset.sum_nonneg
    intro c _
    apply mul_nonneg (by simpa only [hH0] using hppos c.length)
    exact Finset.prod_nonneg fun j _ ↦ hHpos (c.partSize j)

private theorem compositionDerivativesNonneg {f g : ℝ → ℝ}
    (hf : AnalyticAt ℝ f 0) (hg : AnalyticAt ℝ g 0) (hf0 : f 0 = 0)
    (hfpos : ∀ n : ℕ, 0 ≤ iteratedDeriv n f 0)
    (hgpos : ∀ n : ℕ, 0 ≤ iteratedDeriv n g 0) :
    ∀ n : ℕ, 0 ≤ iteratedDeriv n (g ∘ f) 0 := by
  intro n
  have hgCd : ContDiffAt ℝ ∞ g (f 0) := by simpa only [hf0] using hg.contDiffAt
  rw [iteratedDeriv_comp_eq_sum_orderedFinpartition hgCd hf.contDiffAt (by simp)]
  apply Finset.sum_nonneg
  intro c _
  apply mul_nonneg (by simpa only [hf0] using hgpos c.length)
  exact Finset.prod_nonneg fun j _ ↦ hfpos (c.partSize j)

private theorem goursatQuadraticMajorant (a b M R ρ m : ℝ)
    (ha : 0 ≤ a) (hb : 0 < b) (hM : 0 ≤ M) (hR : 0 < R)
    (hρ : 0 < ρ) (hm : 0 < m) :
    ∃ v : ℝ → ℝ, v 0 = 0 ∧ AnalyticAt ℝ v 0 ∧ deriv v 0 = 0 ∧
      (∀ᶠ t in 𝓝 0,
        b * deriv v t - a * (deriv v t) ^ 2 =
          M * (t / ρ + m * v t) / (R - (t / ρ + m * v t))) ∧
      ∀ n : ℕ, 0 ≤ iteratedDeriv n v 0 := by
  obtain ⟨g, hg0, hga, hgeq, hgpos⟩ := goursatBranchWithPositiveDerivatives a b M R ha hb hM hR
  let F : ℝ → ℝ := fun x ↦ ρ⁻¹ + m * g x
  have hFa : AnalyticAt ℝ F 0 := analyticAt_const.add (analyticAt_const.mul hga)
  have hFpos : ∀ n : ℕ, 0 ≤ iteratedDeriv n F 0 := by
    intro n
    cases n with
    | zero => simpa [F, hg0] using (inv_nonneg.mpr hρ.le)
    | succ n =>
      change 0 ≤ iteratedDeriv (n + 1) (fun x ↦ ρ⁻¹ + m * g x) 0
      rw [iteratedDeriv_const_add (Nat.succ_pos n), iteratedDeriv_const_mul_field]
      exact mul_nonneg hm.le (hgpos (n + 1))
  obtain ⟨w, hw0, hwa, hdw⟩ := odeGermForMajorant hFa
  have hwpos := majorantDerivativeNonneg hFa hwa hw0 hdw hFpos
  let v : ℝ → ℝ := fun t ↦ (w t - t / ρ) / m
  have hv0 : v 0 = 0 := by simp [v, hw0]
  have hva : AnalyticAt ℝ v 0 :=
    (hwa.sub (analyticAt_id.div analyticAt_const hρ.ne')).div analyticAt_const hm.ne'
  have hS (t : ℝ) : t / ρ + m * v t = w t := by
    dsimp only [v]
    field_simp [hm.ne']
    ring
  have hdv : ∀ᶠ t in 𝓝 0, HasDerivAt v (g (w t)) t := by
    filter_upwards [hdw] with t ht
    have hd := (ht.sub ((hasDerivAt_id t).div_const ρ)).div_const m
    convert hd using 1
    · rfl
    · dsimp only [F]
      field_simp [hm.ne', hρ.ne']
      ring
  have hvd0 : deriv v 0 = 0 := by simpa only [hw0, hg0] using hdv.self_of_nhds.deriv
  have hquad : ∀ᶠ t in 𝓝 0,
      b * deriv v t - a * (deriv v t) ^ 2 =
        M * (t / ρ + m * v t) / (R - (t / ρ + m * v t)) := by
    have hwcont : Tendsto w (𝓝 0) (𝓝 0) := by
      have hc : Tendsto w (𝓝 0) (𝓝 (w 0)) := hwa.continuousAt
      rwa [hw0] at hc
    filter_upwards [hdv, hwcont.eventually hgeq] with t ht hgt
    rw [ht.deriv, hS]
    exact hgt
  refine ⟨v, hv0, hva, hvd0, hquad, ?_⟩
  have hDvg : deriv v =ᶠ[𝓝 0] g ∘ w := hdv.mono fun t ht ↦ ht.deriv
  intro n
  cases n with
  | zero => simpa only [iteratedDeriv_zero, hv0] using (le_refl (0 : ℝ))
  | succ n =>
    rw [iteratedDeriv_succ', (hDvg.iteratedDeriv n).self_of_nhds]
    exact compositionDerivativesNonneg hwa hga hw0 hwpos hgpos n

/-- The actual analytic scalar majorant in Gantumur's proof of first-order CK.

Source: Gantumur, notes2, Theorem18 proof, equations48–51 (printed p10).
For nonnegative a and M with aM<1, positive R, ρ and m, construct a real analytic v with
v(0)=v′(0)=0 satisfying the actual rational Goursat equation near0. Every actual Taylor
derivative of v at0 is nonnegative. In the PDE application a is the spatial count times
mρ/R; the choice of a sufficiently small ρ is a separate elementary step.

Proof: actual scalar ODE existence applied to p′=1/(b−2ap), b=1−aM>0, gives an analytic
quadratic inverse germ. The native geometric power series has nonnegative derivatives at0;
Faà di Bruno and strong induction pass this property to p. Integrating its actual derivative
identity proves bp−ap²=z. Compose this inverse with Mz/(R−z) to obtain the analytic positive
branch g in equation50. Solve w′=1/ρ+mg(w), w(0)=0, using the proved scalar analytic ODE,
and put v(t)=(w(t)−t/ρ)/m. Then v′=g(w), w=t/ρ+mv, and all derivatives of v are nonnegative
by the actual composition formula. The branch identity gives the quadratic equation49;
continuity and the values at0 make the actual rational denominators nonzero near0, where
algebra gives equation48. No majorant, solution, coefficient positivity or convergence is
assumed. This helper does not assert coefficient domination for the original PDE. -/
theorem collarGoursatAnalyticMajorant (a M R ρ m : ℝ)
    (ha : 0 ≤ a) (hM : 0 ≤ M) (hR : 0 < R) (hρ : 0 < ρ) (hm : 0 < m)
    (hsmall : a * M < 1) :
    ∃ v : ℝ → ℝ, v 0 = 0 ∧ AnalyticAt ℝ v 0 ∧ deriv v 0 = 0 ∧
      (∀ᶠ t in 𝓝 0,
        deriv v t = M / ((1 - (t / ρ + m * v t) / R) * (1 - a * deriv v t)) - M) ∧
      ∀ n : ℕ, 0 ≤ iteratedDeriv n v 0 := by
  obtain ⟨v, hv0, hva, hvd0, hquad, hpos⟩ :=
    goursatQuadraticMajorant a (1 - a * M) M R ρ m ha (sub_pos.mpr hsmall) hM hR hρ hm
  refine ⟨v, hv0, hva, hvd0, ?_, hpos⟩
  let S : ℝ → ℝ := fun t ↦ t / ρ + m * v t
  have hS0 : S 0 = 0 := by simp [S, hv0]
  have hSc : ContinuousAt S 0 :=
    (continuousAt_id.div_const ρ).add (continuousAt_const.mul hva.continuousAt)
  have hDc : ContinuousAt (deriv v) 0 := hva.deriv.continuousAt
  have hdenc : ContinuousAt (fun t ↦ (1 - S t / R) * (1 - a * deriv v t)) 0 :=
    (continuousAt_const.sub (hSc.div_const R)).mul
      (continuousAt_const.sub (continuousAt_const.mul hDc))
  have hden : ∀ᶠ t in 𝓝 0, (1 - S t / R) * (1 - a * deriv v t) ≠ 0 :=
    hdenc.eventually_ne (by simp [hS0, hvd0])
  have hRS : ∀ᶠ t in 𝓝 0, R - S t ≠ 0 :=
    (continuousAt_const.sub hSc).eventually_ne
      (by simpa only [Pi.sub_apply, hS0, sub_zero] using hR.ne')
  filter_upwards [hquad, hden, hRS] with t ht hd htR
  change (1 - a * M) * deriv v t - a * (deriv v t) ^ 2 =
    M * S t / (R - S t) at ht
  have ht' := (eq_div_iff htR).mp ht
  change deriv v t = M / ((1 - S t / R) * (1 - a * deriv v t)) - M
  rw [eq_sub_iff_add_eq]
  apply (eq_div_iff hd).mpr
  field_simp [hR.ne']
  nlinarith [ht']

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarGoursatAnalyticMajorant
