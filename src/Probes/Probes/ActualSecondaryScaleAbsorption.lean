import GlobalEmbedding.Offline.OneStepScaleBounds

/-!
# Secondary total-jet bounds fit the original probe error scale

The secondary construction has actual total derivatives. Observing `r`
spatial and `s` parameter directions therefore costs `tau ^ (r+s)`.
The exact comparison below shows when this is sufficient for the original
probe error `delta * tau ^ (1-r) * (tau/ell)`. The spatial order cancels.
The original stage scales are retained for every `k >= 10`; no numerical
specialization to the first stage replaces the general proof.
-/

noncomputable section
namespace GlobalEmbedding.Continuation

/-- Exact ratio for every spatial and parameter order, with no division by
the amplitude. It therefore also covers zero secondary amplitude. -/
theorem secondary_total_jet_probe_ratio
    (delta tau ell : ℝ) (htau : tau ≠ 0) (hell : ell ≠ 0) (r s : ℕ) :
    delta ^ 2 / tau ^ (r + s) =
      (delta * tau / tau ^ r * (tau / ell)) * (delta * ell / tau ^ (s + 2)) := by
  field_simp [pow_add, htau, hell]
  ring

/-- A total-order secondary estimate can be absorbed into the original
spatial probe error scale without imposing an anisotropic secondary bound. -/
theorem secondary_total_jet_probe_absorption
    (delta tau ell C : ℝ) (hdelta : 0 ≤ delta) (htau : 0 < tau)
    (hell : 0 < ell) (hC : 0 ≤ C) (r s : ℕ)
    (hsmall : delta * ell ≤ tau ^ (s + 2)) :
    C * delta ^ 2 / tau ^ (r + s) ≤
      C * (delta * tau / tau ^ r) * (tau / ell) := by
  have hratio : delta * ell / tau ^ (s + 2) ≤ 1 :=
    (div_le_one (pow_pos htau _)).2 hsmall
  calc
    _ = C * ((delta * tau / tau ^ r * (tau / ell)) *
        (delta * ell / tau ^ (s + 2))) := by
      rw [← secondary_total_jet_probe_ratio delta tau ell htau.ne' hell.ne' r s]
      ring
    _ ≤ C * ((delta * tau / tau ^ r * (tau / ell)) * 1) := by
      apply mul_le_mul_of_nonneg_left _ hC
      exact mul_le_mul_of_nonneg_left hratio (by positivity)
    _ = _ := by ring

/-- The exact parameter-order budget at the original repair scales. The
integer inequality is equivalent to `k + 11/10 >= (6/5)(s+2)`. -/
theorem secondary_original_scale_parameter_budget
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k s : ℕ)
    (hbudget : 12 * s + 13 ≤ 10 * k) :
    t ^ k * t ^ (11 / 10 : ℝ) ≤ (t ^ (6 / 5 : ℝ)) ^ (s + 2) := by
  rw [← Real.rpow_natCast t k, ← Real.rpow_add ht,
    ← Real.rpow_natCast (t ^ (6 / 5 : ℝ)) (s + 2), ← Real.rpow_mul ht.le]
  apply Real.rpow_le_rpow_of_exponent_ge ht ht1
  have hb : (12 : ℝ) * (s : ℝ) + 13 ≤ 10 * (k : ℝ) := by exact_mod_cast hbudget
  push_cast
  linarith

/-- At every original stage `k >= 10`, all parameter orders through seven
fit this absorption. In particular both first and second parameter response
are available, at every spatial observation order allowed by the solver. -/
theorem secondary_original_scale_parameter_budget_seven
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k s : ℕ)
    (hk : 10 ≤ k) (hs : s ≤ 7) :
    t ^ k * t ^ (11 / 10 : ℝ) ≤ (t ^ (6 / 5 : ℝ)) ^ (s + 2) :=
  secondary_original_scale_parameter_budget ht ht1 k s (by omega)

/-- Uniform in the spatial order, with the exact original scales. Constants
are not absorbed by changing `k`, `ell`, `tau`, or the allowed error formula. -/
theorem secondary_original_scale_probe_absorption
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k r s : ℕ)
    (hbudget : 12 * s + 13 ≤ 10 * k) (C : ℝ) (hC : 0 ≤ C) :
    C * (t ^ k) ^ 2 / (t ^ (6 / 5 : ℝ)) ^ (r + s) ≤
      C * (t ^ k * t ^ (6 / 5 : ℝ) / (t ^ (6 / 5 : ℝ)) ^ r) *
        (t ^ (6 / 5 : ℝ) / t ^ (11 / 10 : ℝ)) :=
  secondary_total_jet_probe_absorption (t ^ k) (t ^ (6 / 5 : ℝ))
    (t ^ (11 / 10 : ℝ)) C (pow_nonneg ht.le k)
    (Real.rpow_pos_of_pos ht _) (Real.rpow_pos_of_pos ht _) hC r s
    (secondary_original_scale_parameter_budget ht ht1 k s hbudget)

/-- The first-parameter spatial Hessian has exactly the originally stated
`sigma * tau/ell` allowance, rather than an unscaled error surrogate. -/
theorem secondary_original_scale_hessian_response
    {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1) (k : ℕ) (hk : 10 ≤ k)
    (C : ℝ) (hC : 0 ≤ C) :
    C * (t ^ k) ^ 2 / (t ^ (6 / 5 : ℝ)) ^ 3 ≤
      C * (t ^ k / t ^ (6 / 5 : ℝ)) *
        (t ^ (6 / 5 : ℝ) / t ^ (11 / 10 : ℝ)) := by
  have h := secondary_original_scale_probe_absorption ht ht1 k 2 1 (by omega) C hC
  have he : t ^ k * t ^ (6 / 5 : ℝ) / (t ^ (6 / 5 : ℝ)) ^ 2 =
      t ^ k / t ^ (6 / 5 : ℝ) := by
    field_simp [(Real.rpow_pos_of_pos ht (6 / 5 : ℝ)).ne']
  simpa only [show 2 + 1 = 3 from rfl, he] using h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.secondary_total_jet_probe_ratio
#print axioms GlobalEmbedding.Continuation.secondary_total_jet_probe_absorption
#print axioms GlobalEmbedding.Continuation.secondary_original_scale_parameter_budget
#print axioms GlobalEmbedding.Continuation.secondary_original_scale_probe_absorption
#print axioms GlobalEmbedding.Continuation.secondary_original_scale_hessian_response
