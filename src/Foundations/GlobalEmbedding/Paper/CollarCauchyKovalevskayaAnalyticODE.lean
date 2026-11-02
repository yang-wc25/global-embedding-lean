import Mathlib.Analysis.Calculus.FDeriv.Analytic
import Mathlib.Analysis.Analytic.OfScalars
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Analytic
import Mathlib.Analysis.ODE.ExistUnique

open scoped Topology NNReal ENNReal ContDiff
open Filter Set FormalMultilinearSeries

/-!
# Scalar autonomous analytic Cauchy problems

Source: Gantumur, Math580 notes2, Theorem9, used in the proof of Theorem18.
The complete original scalar ODE is proved without assuming any solution or any separate
analytic ODE existence theorem. The primitive is an actual convergent coefficient construction.
-/

namespace GlobalEmbedding.Paper

/-- Integrate the actual scalar power series: its new coefficient of degree n+1 is the old
coefficient divided by n+1. A positive radius survives by a direct norm bound. The native
power-series derivative and evaluation at1 prove the actual derivative identity near0. -/
private theorem collarAnalyticPrimitiveAtZero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ P : ℝ → ℝ, P 0 = 0 ∧ AnalyticAt ℝ P 0 ∧
      ∀ᶠ x in 𝓝 0, HasDerivAt P (f x) x := by
  obtain ⟨p, ρ, hp⟩ := hf
  obtain ⟨r, hr0, hr⟩ := ENNReal.lt_iff_exists_nnreal_btwn.mp hp.r_pos
  have hrp : (r : ℝ≥0∞) < p.radius := hr.trans_le hp.r_le
  obtain ⟨C, hC0, hC⟩ := p.norm_mul_pow_le_of_lt_radius hrp
  let c : ℕ → ℝ := fun n ↦ if n = 0 then 0 else p.coeff (n - 1) / (n : ℝ)
  let q := FormalMultilinearSeries.ofScalars ℝ c
  have hrpos : 0 < (r : ℝ) := by exact_mod_cast hr0
  have hqcoeff (n : ℕ) : q.coeff (n + 1) = p.coeff n / (n + 1 : ℝ) := by
    simp [q, c]
  have hqr : (r : ℝ≥0∞) ≤ q.radius := by
    apply q.le_radius_of_bound (C * r)
    intro n
    cases n with
    | zero =>
      simpa [q, c] using mul_nonneg (le_of_lt hC0) (le_of_lt hrpos)
    | succ n =>
      have hn : (1 : ℝ) ≤ n + 1 := le_add_of_nonneg_left (Nat.cast_nonneg n)
      have hd : ‖p.coeff n / (n + 1 : ℝ)‖ ≤ ‖p.coeff n‖ := by
        rw [norm_div]
        simpa only [Real.norm_of_nonneg (show 0 ≤ (n : ℝ) + 1 from le_trans zero_le_one hn)]
          using div_le_self (norm_nonneg (p.coeff n)) hn
      calc
        ‖q (n + 1)‖ * (r : ℝ) ^ (n + 1) ≤
            ‖p.coeff n‖ * (r : ℝ) ^ (n + 1) := by
          rw [norm_apply_eq_norm_coef, hqcoeff]
          gcongr
        _ = (‖p n‖ * (r : ℝ) ^ n) * r := by
          rw [norm_apply_eq_norm_coef, pow_succ, mul_assoc]
        _ ≤ C * r := mul_le_mul_of_nonneg_right (hC n) (le_of_lt hrpos)
  have hqpos : 0 < q.radius := hr0.trans_le hqr
  refine ⟨q.sum, ?_, (q.hasFPowerSeriesOnBall hqpos).analyticAt, ?_⟩
  · simp only [FormalMultilinearSeries.sum, apply_eq_pow_smul_coeff, smul_eq_mul]
    calc
      _ = ∑' _n : ℕ, (0 : ℝ) := tsum_congr fun n ↦ by
        cases n <;> simp [q, c]
      _ = 0 := tsum_zero
  have hball : ∀ᶠ x : ℝ in 𝓝 0, ‖x‖ₑ < (r : ℝ≥0∞) := by
    filter_upwards [Metric.eball_mem_nhds (0 : ℝ) hr0] with x hx
    simpa only [Metric.mem_eball, edist_zero_right] using hx
  filter_upwards [hball] with x hx
  have hqx := (q.hasFDerivAt_sum (hx.trans_le hqr)).hasDerivAt
  convert hqx using 1
  have hs : HasSum (fun n : ℕ ↦ x ^ n * p.coeff n) (f x) := by
    simpa [apply_eq_pow_smul_coeff] using hp.hasSum
      (by simpa only [Metric.mem_eball, edist_zero_right] using hx.trans hr)
  have hqs := ((q.hasFPowerSeriesOnBall hqpos).fderiv.hasSum
    (by simpa only [Metric.mem_eball, edist_zero_right] using hx.trans_le hqr)).map
      (ContinuousLinearMap.apply ℝ ℝ (1 : ℝ)) (ContinuousLinearMap.continuous _)
  simp only [zero_add] at hqs
  change HasSum (fun n : ℕ ↦ (q.derivSeries n fun _ ↦ x) 1)
    ((fderiv ℝ q.sum x) 1) at hqs
  rw [q.fderiv_sum (hx.trans_le hqr)] at hqs
  have ht : (fun n : ℕ ↦ (q.derivSeries n fun _ ↦ x) 1) =
      (fun n : ℕ ↦ x ^ n * p.coeff n) := by
    funext n
    simp only [apply_eq_pow_smul_coeff, _root_.smul_apply, derivSeries_coeff_one, hqcoeff,
      smul_eq_mul, nsmul_eq_mul, Nat.cast_add, Nat.cast_one]
    field_simp
  rw [ht] at hqs
  exact hs.unique hqs


/-- The analytic vector field has a genuine Lipschitz bound on a neighborhood of its initial
value. Continuous solution germs remain in that neighborhood, so the native local ODE
uniqueness theorem applies to their actual derivatives. -/
private theorem collarAnalyticODEGermUnique {f u v : ℝ → ℝ} {y₀ : ℝ} (hf : AnalyticAt ℝ f y₀)
    (hu : ContinuousAt u 0) (hv : ContinuousAt v 0) (hu0 : u 0 = y₀) (hv0 : v 0 = y₀)
    (hdu : ∀ᶠ t in 𝓝 0, HasDerivAt u (f (u t)) t)
    (hdv : ∀ᶠ t in 𝓝 0, HasDerivAt v (f (v t)) t) : u =ᶠ[𝓝 0] v := by
  obtain ⟨K, S, hS, hLip⟩ := hf.hasStrictDerivAt.hasStrictFDerivAt.exists_lipschitzOnWith
  have huS : ∀ᶠ t in 𝓝 0, u t ∈ S := by
    apply hu.preimage_mem_nhds
    simpa only [hu0] using hS
  have hvS : ∀ᶠ t in 𝓝 0, v t ∈ S := by
    apply hv.preimage_mem_nhds
    simpa only [hv0] using hS
  exact ODE_solution_unique_of_eventually
    (v := fun _ ↦ f) (s := fun _ ↦ S) (K := K)
    (Eventually.of_forall fun _ ↦ hLip) (hdu.and huS) (hdv.and hvS) (hu0.trans hv0.symm)

/-- At an equilibrium take the constant solution. Otherwise integrate the analytic reciprocal
of the translated vector field and invert this actual primitive analytically. The inverse
identity and its true derivative show that the inverse curve solves the original ODE. Native
Lipschitz uniqueness compares every other analytic solution germ with this constructed one. -/
private theorem collarAnalyticODEGerm {f : ℝ → ℝ} {y₀ : ℝ} (hf : AnalyticAt ℝ f y₀) :
    ∃ u : ℝ → ℝ, u 0 = y₀ ∧ AnalyticAt ℝ u 0 ∧
      (∀ᶠ t in 𝓝 0, HasDerivAt u (f (u t)) t) ∧
      ∀ v : ℝ → ℝ, AnalyticAt ℝ v 0 → v 0 = y₀ →
        (∀ᶠ t in 𝓝 0, HasDerivAt v (f (v t)) t) → u =ᶠ[𝓝 0] v := by
  have hex : ∃ u : ℝ → ℝ, u 0 = y₀ ∧ AnalyticAt ℝ u 0 ∧
      ∀ᶠ t in 𝓝 0, HasDerivAt u (f (u t)) t := by
    by_cases hzero : f y₀ = 0
    · exact ⟨fun _ ↦ y₀, rfl, analyticAt_const,
        Eventually.of_forall fun t ↦ by simpa [hzero] using hasDerivAt_const t y₀⟩
    have hshift : AnalyticAt ℝ (fun x : ℝ ↦ f (y₀ + x)) 0 := by
      have hf' : AnalyticAt ℝ f (y₀ + 0) := by simpa only [add_zero] using hf
      exact hf'.comp (analyticAt_const.add analyticAt_id)
    obtain ⟨P, hP0, hPa, hdP⟩ :=
      collarAnalyticPrimitiveAtZero (hshift.inv (by simpa only [add_zero] using hzero))
    have hdP0 : deriv P 0 = (f y₀)⁻¹ := by
      simpa using hdP.self_of_nhds.deriv
    have hdnz : deriv P 0 ≠ 0 := by simpa [hdP0] using hzero
    let z := hPa.hasStrictDerivAt.localInverse P (deriv P 0) 0 hdnz
    have hza : AnalyticAt ℝ z 0 := by
      simpa only [hP0] using hPa.analyticAt_localInverse hdnz
    have hz0 : z 0 = 0 := by
      have hleft : z (P 0) = 0 :=
        (hPa.hasStrictDerivAt.eventually_left_inverse hdnz).self_of_nhds
      simpa only [hP0] using hleft
    have hzcont : Tendsto z (𝓝 0) (𝓝 0) := by
      have hc : Tendsto z (𝓝 0) (𝓝 (z 0)) := hza.continuousAt
      rwa [hz0] at hc
    have hright : (P ∘ z) =ᶠ[𝓝 0] id := by
      change ∀ᶠ t in 𝓝 0, P (z t) = t
      simpa only [hP0] using hPa.hasStrictDerivAt.eventually_right_inverse hdnz
    have hdPz := hzcont.eventually hdP
    have hfnz : ∀ᶠ t in 𝓝 0, f (y₀ + z t) ≠ 0 := by
      have hf' : ContinuousAt f (y₀ + z 0) := by
        simpa only [hz0, add_zero] using hf.continuousAt
      have hinner : ContinuousAt (fun t : ℝ ↦ y₀ + z t) 0 :=
        continuousAt_const.add hza.continuousAt
      have hfc : ContinuousAt (fun t ↦ f (y₀ + z t)) 0 :=
        hf'.comp (f := fun t : ℝ ↦ y₀ + z t) (x := 0) hinner
      exact hfc.eventually_ne (by simpa only [hz0, add_zero] using hzero)
    have hdz : ∀ᶠ t in 𝓝 0, HasDerivAt z (f (y₀ + z t)) t := by
      filter_upwards [hdPz, hfnz, hza.eventually_analyticAt, hright.eventuallyEq_nhds]
        with t hP hfnt hzt hrt
      have hzder := hP.of_local_left_inverse hzt.continuousAt (inv_ne_zero hfnt) hrt
      simpa only [Pi.inv_apply, inv_inv] using hzder
    refine ⟨fun t ↦ y₀ + z t, by simp [hz0], analyticAt_const.add hza, ?_⟩
    filter_upwards [hdz] with t ht
    simpa using ht.const_add y₀
  obtain ⟨u, hu0, hua, hdu⟩ := hex
  refine ⟨u, hu0, hua, hdu, ?_⟩
  intro v hva hv0 hdv
  exact collarAnalyticODEGermUnique hf hua.continuousAt hva.continuousAt hu0 hv0 hdu hdv


/-- Every real analytic scalar autonomous vector field has a local real analytic solution
through its given initial value, unique among local real analytic solutions.

Source: Gantumur, Math580 lecture notes2, Theorem9 and its use in Theorem18.
Proof: integrate the actual convergent reciprocal series and use its analytic local inverse
when the initial vector field is nonzero. At a zero take the constant solution. Local
Lipschitz uniqueness proves equality of any two solution germs. Finally choose a common
positive real ball on which the actual curve is analytic and solves the equation, and shrink
both competitor domains to a positive ball for the explicit local uniqueness conclusion.
No convergence or existence assertion is left as an assumption or an unproved theorem. -/
theorem collarCauchyKovalevskayaAnalyticODE {f : ℝ → ℝ} {y₀ : ℝ} (hf : AnalyticAt ℝ f y₀) :
    ∃ ε > 0, ∃ u : ℝ → ℝ, u 0 = y₀ ∧
      AnalyticOnNhd ℝ u (Metric.ball 0 ε) ∧
      (∀ t ∈ Metric.ball 0 ε, HasDerivAt u (f (u t)) t) ∧
      ∀ v : ℝ → ℝ, ∀ η > 0, v 0 = y₀ →
        AnalyticOnNhd ℝ v (Metric.ball 0 η) →
        (∀ t ∈ Metric.ball 0 η, HasDerivAt v (f (v t)) t) →
        ∃ δ > 0, δ ≤ ε ∧ δ ≤ η ∧ EqOn u v (Metric.ball 0 δ) := by
  obtain ⟨u, hu0, hua, hdu, huniq⟩ := collarAnalyticODEGerm hf
  obtain ⟨ε, hε, hprop⟩ := Metric.eventually_nhds_iff_ball.mp
    (hua.eventually_analyticAt.and hdu)
  refine ⟨ε, hε, u, hu0, fun t ht ↦ (hprop t ht).1, fun t ht ↦ (hprop t ht).2, ?_⟩
  intro v η hη hv0 hva hdv
  have hdvg : ∀ᶠ t in 𝓝 0, HasDerivAt v (f (v t)) t :=
    eventually_of_mem (Metric.ball_mem_nhds 0 hη) hdv
  have heq := huniq v (hva 0 (Metric.mem_ball_self hη)) hv0 hdvg
  obtain ⟨δ, hδ, heqδ⟩ := Metric.eventually_nhds_iff_ball.mp heq
  refine ⟨min δ (min ε η), lt_min hδ (lt_min hε hη),
    (min_le_right _ _).trans (min_le_left _ _),
    (min_le_right _ _).trans (min_le_right _ _), ?_⟩
  intro t ht
  exact heqδ t (Metric.ball_subset_ball (min_le_left _ _) ht)

/-- Public access to the existing convergent scalar analytic primitive construction.
This wrapper reuses its original proof without changing the scalar ODE declarations. -/
theorem collar_analytic_primitive_at_zero {f : ℝ → ℝ} (hf : AnalyticAt ℝ f 0) :
    ∃ P : ℝ → ℝ, P 0 = 0 ∧ AnalyticAt ℝ P 0 ∧
      ∀ᶠ x in 𝓝 0, HasDerivAt P (f x) x :=
  collarAnalyticPrimitiveAtZero hf

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCauchyKovalevskayaAnalyticODE

#print axioms GlobalEmbedding.Paper.collar_analytic_primitive_at_zero
