import Probes.ActualJointFiniteResidual

/-!
# Native operator for the exact physical finite residual rows

The 11 row has the original factor two, the two symmetric mixed rows have
factor one, and all transverse rows vanish. The operator norm is at most
two independently of the dimension and number of secondary records.
-/

noncomputable section
open Set GlobalEmbedding.Paper
open scoped ContDiff
namespace GlobalEmbedding.Continuation

variable {m : ℕ}

/-- The original physical row factors, as a fixed real continuous linear
map between the native complex finite-coordinate spaces. -/
def actualModeResidualRows : (Fin (m + 1) → ℂ) →L[ℝ]
    (Fin (m + 1) → Fin (m + 1) → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.pi fun j =>
    if i = 0 then
      if j = 0 then (2 : ℝ) • ContinuousLinearMap.proj 0 else ContinuousLinearMap.proj j
    else if j = 0 then ContinuousLinearMap.proj i else 0

@[simp] theorem actualModeResidualRows_apply (v : Fin (m + 1) → ℂ) (i j : Fin (m + 1)) :
    actualModeResidualRows v i j =
      if i = 0 then (if j = 0 then 2 * v 0 else v j) else if j = 0 then v i else 0 := by
  simp only [actualModeResidualRows, ContinuousLinearMap.pi_apply]
  split_ifs <;> simp

theorem actualModeResidualRows_norm_le : ‖actualModeResidualRows (m := m)‖ ≤ 2 := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by norm_num)
  intro v
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * ‖v‖)).2
  intro i
  apply (pi_norm_le_iff_of_nonneg (by positivity : 0 ≤ 2 * ‖v‖)).2
  intro j
  rw [actualModeResidualRows_apply]
  split_ifs
  · simpa only [norm_mul, Complex.norm_ofNat] using
      mul_le_mul_of_nonneg_left (norm_le_pi_norm v 0) (by norm_num : (0 : ℝ) ≤ 2)
  · exact (norm_le_pi_norm v j).trans (by nlinarith [norm_nonneg v])
  · exact (norm_le_pi_norm v i).trans (by nlinarith [norm_nonneg v])
  · simp

/-- Exact physical row conversion preserves all native joint residual jets,
with only the original numerical factor two. -/
theorem actual_mode_residual_rows_weighted_jets
    {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X]
    (v : X → Fin (m + 1) → ℂ) (O S : Set X) (hO : IsOpen O) (hSO : S ⊆ O)
    (hv : ContDiffOn ℝ ∞ v O) (n : ℕ) (ell K : ℝ) (hell : 0 ≤ ell) (hK : 0 ≤ K)
    (hvb : ∀ r ≤ n, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r v z‖ ≤ K) :
    ContDiffOn ℝ ∞ (fun z => actualModeResidualRows (v z)) O ∧
      ∀ r ≤ n, ∀ z ∈ S, ell ^ r * ‖iteratedFDeriv ℝ r
        (fun w => actualModeResidualRows (v w)) z‖ ≤ 2 * K := by
  refine ⟨actualModeResidualRows.contDiff.comp_contDiffOn hv, ?_⟩
  intro r hr z hz
  exact (slow_linear_jet_bound actualModeResidualRows O hO v hv r ell K hell z
    (hSO hz) (hvb r hr z hz)).trans
      (mul_le_mul_of_nonneg_right actualModeResidualRows_norm_le hK)

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.actualModeResidualRows_norm_le
#print axioms GlobalEmbedding.Continuation.actual_mode_residual_rows_weighted_jets
