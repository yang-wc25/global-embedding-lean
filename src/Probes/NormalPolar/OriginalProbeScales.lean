import NormalPolar.FullResponseScales

/-!
# The literal slow scale of the original paired-probe proof

The paper uses delta=t^10, tau=t^(6/5), and ell=t^(11/10).
The older `FullResponseScales` has a valid auxiliary specialization ell=t;
its one-fifth error must not be substituted for the original one-tenth
error without proving stronger slow-jet bounds.  This module keeps the
paper's ell and all its weighted-jet hypotheses unchanged.

The scale identities require only t>0.  The original solver's additional
ell<=1 and tau<=ell hypotheses are explicitly discharged when t<=1.
Nothing here replaces an already chosen parameter ball or scale interval.
-/

noncomputable section
open Set Filter
open scoped Topology

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Upgrade

theorem probe_tau_div_original_ell (t : ℝ) (ht : 0 < t) :
    t ^ ((6 : ℝ) / 5) / t ^ ((11 : ℝ) / 10) = |t| ^ ((1 : ℝ) / 10) := by
  rw [← Real.rpow_sub ht, abs_of_pos ht]
  norm_num

theorem probe_original_scale_conditions (t : ℝ) (ht : 0 < t) (ht1 : t ≤ 1) :
    0 < t ^ ((11 : ℝ) / 10) ∧ t ^ ((11 : ℝ) / 10) ≤ 1 ∧
      0 < t ^ ((6 : ℝ) / 5) ∧
      t ^ ((6 : ℝ) / 5) ≤ t ^ ((11 : ℝ) / 10) := by
  exact ⟨Real.rpow_pos_of_pos ht _, Real.rpow_le_one ht.le ht1 (by norm_num),
    Real.rpow_pos_of_pos ht _, Real.rpow_le_rpow_of_exponent_ge ht ht1 (by norm_num)⟩

theorem probe_delta_mul_tau_eq_value_scale (t : ℝ) (ht : 0 < t) :
    t ^ (10 : ℕ) * t ^ ((6 : ℝ) / 5) = t ^ ((56 : ℝ) / 5) := by
  rw [← Real.rpow_natCast, ← Real.rpow_add ht]
  norm_num

theorem probe_delta_div_tau_sq_eq_C3_scale (t : ℝ) (ht : 0 < t) :
    t ^ (10 : ℕ) / (t ^ ((6 : ℝ) / 5)) ^ 2 = t ^ ((38 : ℝ) / 5) := by
  rw [← Real.rpow_natCast t 10, ← Real.rpow_natCast (t ^ ((6 : ℝ) / 5)) 2,
    ← Real.rpow_mul ht.le, ← Real.rpow_sub ht]
  norm_num

/-- On the original slow scale the actual Hessian error is sigma times a
one-tenth modulus.  The input is an already proved *raw native* response;
there is no normal identification or identified second form in it. -/
theorem native_hessian_response_paper_scales
    {Y : Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
    (t : ℝ) (ht : 0 < t) (b : Bool) (theta C : ℝ) (R H : Y)
    (h : ‖R - ((t ^ (10 : ℕ) / t ^ ((6 : ℝ) / 5)) *
        (if b then Real.sin theta else Real.cos theta)) • H‖ ≤
      (t ^ (10 : ℕ) / t ^ ((6 : ℝ) / 5)) *
        (t ^ ((6 : ℝ) / 5) / t ^ ((11 : ℝ) / 10)) * C) :
    ‖R - (t ^ ((44 : ℝ) / 5) * probeTrig b theta) • H‖ ≤
      t ^ ((44 : ℝ) / 5) * (C * |t| ^ ((1 : ℝ) / 10)) := by
  rw [probe_delta_div_tau_eq_sigma t ht, probe_tau_div_original_ell t ht] at h
  convert h using 1
  · rfl
  · ring

/-- Actual Hessian coordinate transport also has its first-jet term.  On
the same original scales that term contributes tau, not a new assumption
that it vanishes. -/
theorem native_hessian_chart_error_paper_scales
    (t : ℝ) (ht : 0 < t) (CH C1 B1 B2 : ℝ) :
    ((t ^ (10 : ℕ) / t ^ ((6 : ℝ) / 5)) *
        (t ^ ((6 : ℝ) / 5) / t ^ ((11 : ℝ) / 10)) * CH) * B1 ^ 2 +
      (t ^ (10 : ℕ) * C1) * B2 =
      t ^ ((44 : ℝ) / 5) *
        (CH * B1 ^ 2 * |t| ^ ((1 : ℝ) / 10) +
          C1 * B2 * |t| ^ ((6 : ℝ) / 5)) := by
  rw [probe_delta_div_tau_eq_sigma t ht, probe_tau_div_original_ell t ht,
    abs_of_pos ht]
  have hdelta : t ^ (10 : ℕ) = t ^ ((44 : ℝ) / 5) * t ^ ((6 : ℝ) / 5) := by
    rw [← Real.rpow_add ht]
    norm_num
  rw [hdelta]
  ring

def originalProbeChartModulus (CH C1 B1 B2 t : ℝ) : ℝ :=
  CH * B1 ^ 2 * |t| ^ ((1 : ℝ) / 10) + C1 * B2 * |t| ^ ((6 : ℝ) / 5)

theorem originalProbeChartModulus_nonneg (CH C1 B1 B2 t : ℝ)
    (hCH : 0 ≤ CH) (hC1 : 0 ≤ C1) (hB2 : 0 ≤ B2) :
    0 ≤ originalProbeChartModulus CH C1 B1 B2 t := by
  unfold originalProbeChartModulus
  positivity

theorem originalProbeChartModulus_tendsto (CH C1 B1 B2 : ℝ) :
    Tendsto (originalProbeChartModulus CH C1 B1 B2) (𝓝[>] 0) (𝓝 0) := by
  have hc : Continuous (originalProbeChartModulus CH C1 B1 B2) := by
    unfold originalProbeChartModulus
    exact (continuous_const.mul
      ((Real.continuous_rpow_const (by norm_num : 0 ≤ (1 : ℝ) / 10)).comp continuous_abs)).add
      (continuous_const.mul
        ((Real.continuous_rpow_const (by norm_num : 0 ≤ (6 : ℝ) / 5)).comp continuous_abs))
  have hz : originalProbeChartModulus CH C1 B1 B2 0 = 0 := by
    simp [originalProbeChartModulus, Real.zero_rpow (by norm_num : (6 : ℝ) / 5 ≠ 0)]
  simpa only [hz] using (hc.tendsto 0).mono_left
    (show 𝓝[>] (0 : ℝ) ≤ 𝓝 0 from inf_le_left)

end GlobalEmbedding.NormalPolar

#print axioms GlobalEmbedding.NormalPolar.native_hessian_response_paper_scales
#print axioms GlobalEmbedding.NormalPolar.native_hessian_chart_error_paper_scales
#print axioms GlobalEmbedding.NormalPolar.originalProbeChartModulus_tendsto
