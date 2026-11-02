import Probes.ActualProbeProfileBounds
import Probes.ActualProbeLocalJets

/-! Native first/second jet extraction from primitive weighted profiles.
These conversions preserve all phase weights and the true Hessian norm. -/
noncomputable section
open scoped ContDiff
namespace GlobalEmbedding.Offline
variable {X Y : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
  [NormedAddCommGroup Y] [NormedSpace ℝ Y]

theorem probe_profile_twojet_of_weighted
    (A : X → Y) (x : X) (ell K : ℝ) (hell : 0 < ell)
    (hb : ∀ n ≤ 2, ell ^ n * ‖iteratedFDeriv ℝ n A x‖ ≤ K) :
    ‖A x‖ ≤ K ∧ ‖fderiv ℝ A x‖ ≤ K / ell ∧
      ‖fderiv ℝ (fderiv ℝ A) x‖ ≤ K / ell ^ 2 := by
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have h2 := hb 2 (by omega)
  simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero] at h0
  simp only [pow_one, norm_iteratedFDeriv_one] at h1
  have hn : ‖iteratedFDeriv ℝ 2 A x‖ = ‖fderiv ℝ (fderiv ℝ A) x‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  rw [hn] at h2
  exact ⟨h0, (le_div_iff₀ hell).mpr (by simpa [mul_comm] using h1),
    (le_div_iff₀ (pow_pos hell 2)).mpr (by simpa [mul_comm] using h2)⟩

/-- True derivatives of psi from weighted derivatives of the original
weighted phase lambda*psi. No unweighted phase budget is added. -/
theorem probe_phase_twojet_of_weighted
    (psi : X → ℝ) (x : X) (hpsi : ContDiffAt ℝ 2 psi x)
    (ell lam M : ℝ) (hell : 0 < ell) (hlam : 0 < lam)
    (hb : ∀ n < 2, ell ^ n * ‖iteratedFDeriv ℝ (n + 1) (fun y ↦ lam * psi y) x‖ ≤ M) :
    0 ≤ M / lam ∧ ‖fderiv ℝ psi x‖ ≤ M / lam ∧
      ‖fderiv ℝ (fderiv ℝ psi) x‖ ≤ (M / lam) / ell := by
  have h0 := hb 0 (by omega)
  have h1 := hb 1 (by omega)
  have hM : 0 ≤ M := le_trans (by positivity) h0
  have ht1 : ContDiffAt ℝ 1 psi x := hpsi.of_le (by norm_num)
  change ell ^ 0 * ‖iteratedFDeriv ℝ 1 (fun y ↦ lam • psi y) x‖ ≤ M at h0
  change ell ^ 1 * ‖iteratedFDeriv ℝ 2 (fun y ↦ lam • psi y) x‖ ≤ M at h1
  rw [iteratedFDeriv_const_smul_apply' ht1, norm_smul, Real.norm_eq_abs,
    abs_of_pos hlam, norm_iteratedFDeriv_one] at h0
  rw [iteratedFDeriv_const_smul_apply' hpsi, norm_smul, Real.norm_eq_abs,
    abs_of_pos hlam] at h1
  have hn : ‖iteratedFDeriv ℝ 2 psi x‖ = ‖fderiv ℝ (fderiv ℝ psi) x‖ := by
    rw [← norm_iteratedFDeriv_fderiv, norm_iteratedFDeriv_one]
  rw [hn] at h1
  simp only [pow_zero, one_mul] at h0
  simp only [pow_one] at h1
  refine ⟨div_nonneg hM hlam.le, (le_div_iff₀ hlam).mpr (by simpa [mul_comm] using h0), ?_⟩
  rw [div_div]
  apply (le_div_iff₀ (mul_pos hlam hell)).mpr
  convert h1 using 1 <;> ring

#print axioms probe_profile_twojet_of_weighted
#print axioms probe_phase_twojet_of_weighted
end GlobalEmbedding.Offline
