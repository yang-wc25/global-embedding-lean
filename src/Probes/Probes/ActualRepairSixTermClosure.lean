import GlobalEmbedding.Offline.OneStepScaleBounds

/-! The proved actual repair bound is expanded into the six literal terms
of (6.7), including both reserve choices. This is only scalar algebra; the
following map consumer inserts the full constructed update. -/

noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped BigOperators
namespace GlobalEmbedding.Continuation

def actualRepairSixCoefficients (C budget inherited : ℝ) : Fin 6 → ℝ
  | 0 => C
  | 1 => C
  | 2 => C*budget
  | 3 => C*inherited
  | 4 => C*budget
  | 5 => C*inherited

theorem actual_repair_six_coefficients_nonneg {C budget inherited : ℝ}
    (hC : 0 ≤ C) (hbudget : 0 ≤ budget) (hinherited : 0 ≤ inherited) (i : Fin 6) :
    0 ≤ actualRepairSixCoefficients C budget inherited i := by
  fin_cases i <;> simp only [actualRepairSixCoefficients] <;> positivity

theorem actual_repair_six_numerators (t : ℝ) (k : ℕ) (C budget inherited : ℝ) :
    C*(t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))+(t^k)^3/t^(6/5 : ℝ)+
      ((t^k)^2+t^k)*(budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+
        inherited*(t^(6/5 : ℝ)/t)^(40*(k+1)))) =
    ∑ i : Fin 6, actualRepairSixCoefficients C budget inherited i*repairErrorNumerator t k i := by
  norm_num [Fin.sum_univ_succ,actualRepairSixCoefficients,repairErrorNumerator]
  ring

theorem actual_repair_six_exact_exponents {t : ℝ} (ht : 0 < t) (k : ℕ) (C budget inherited : ℝ) :
    (((t^(6/5 : ℝ))^(k+1))^2)⁻¹*C*
      (t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))+(t^k)^3/t^(6/5 : ℝ)+
        ((t^k)^2+t^k)*(budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+
          inherited*(t^(6/5 : ℝ)/t)^(40*(k+1)))) =
    ∑ i : Fin 6, actualRepairSixCoefficients C budget inherited i*t^repairErrorExponent k i := by
  calc
    _ = (C*(t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))+(t^k)^3/t^(6/5 : ℝ)+
        ((t^k)^2+t^k)*(budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+
          inherited*(t^(6/5 : ℝ)/t)^(40*(k+1)))))/((t^(6/5 : ℝ))^(k+1))^2 := by ring
    _ = (∑ i : Fin 6, actualRepairSixCoefficients C budget inherited i*repairErrorNumerator t k i)/
        ((t^(6/5 : ℝ))^(k+1))^2 := by rw [actual_repair_six_numerators]
    _ = ∑ i : Fin 6, actualRepairSixCoefficients C budget inherited i*t^repairErrorExponent k i := by
      rw [Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [mul_div_assoc,literal_normalized_repair_error ht]

theorem actual_repair_six_normalized_bound {t C budget inherited : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C) (hbudget : 0 ≤ budget) (hinherited : 0 ≤ inherited)
    (k s : ℕ) (hk : 10 ≤ k) (hs : s ≤ k+1) :
    (((t^(6/5 : ℝ))^s)^2)⁻¹*C*
      (t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))+(t^k)^3/t^(6/5 : ℝ)+
        ((t^k)^2+t^k)*(budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+
          inherited*(t^(6/5 : ℝ)/t)^(40*(k+1)))) ≤
    (2*C+2*C*budget+2*C*inherited)*t^(1/5 : ℝ) := by
  calc
    _ = (C*(t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))+(t^k)^3/t^(6/5 : ℝ)+
        ((t^k)^2+t^k)*(budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+
          inherited*(t^(6/5 : ℝ)/t)^(40*(k+1)))))/((t^(6/5 : ℝ))^s)^2 := by ring
    _ = ∑ i : Fin 6, actualRepairSixCoefficients C budget inherited i*t^repairErrorNumeratorExponent k i/
        ((t^(6/5 : ℝ))^s)^2 := by
      rw [actual_repair_six_numerators,Finset.sum_div]
      apply Finset.sum_congr rfl
      intro i hi
      rw [repairErrorNumerator_eq_rpow ht]
    _ ≤ ∑ i : Fin 6, actualRepairSixCoefficients C budget inherited i*t^(1/5 : ℝ) := by
      apply Finset.sum_le_sum
      intro i hi
      exact normalized_repair_error_le ht ht1
        (actual_repair_six_coefficients_nonneg hC hbudget hinherited i) k s hk hs i
    _ = _ := by
      norm_num [Fin.sum_univ_succ,actualRepairSixCoefficients]
      ring

theorem actual_repair_six_recurrence_bound {t C budget inherited : ℝ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C) (hbudget : 0 ≤ budget) (hinherited : 0 ≤ inherited)
    (k s : ℕ) (hk : 10 ≤ k) (hs : s ≤ k+1) :
    (((t^(6/5 : ℝ))^s)^2)⁻¹*C*
      (t^k*(t^(6/5 : ℝ)/t^(11/10 : ℝ))^(40*(k+1))+(t^k)^3/t^(6/5 : ℝ)+
        ((t^k)^2+t^k)*(budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+
          inherited*(t^(6/5 : ℝ)/t)^(40*(k+1)))) ≤
    (2*C*(1+budget))*t^(1/5 : ℝ)*(1+inherited) := by
  refine (actual_repair_six_normalized_bound ht ht1 hC hbudget hinherited k s hk hs).trans ?_
  have hCI : 0 ≤ 2*C*budget*inherited := by positivity
  have hp : 0 ≤ t^(1/5 : ℝ) := Real.rpow_nonneg ht.le _
  nlinarith [mul_nonneg hCI hp]


theorem actual_repair_stage_scalar_bounds
    {t C budget inherited delta ell tau deltaNext : ℝ} {q : ℕ}
    (ht : 0 < t) (ht1 : t ≤ 1) (hC : 0 ≤ C) (hbudget : 0 ≤ budget) (hinherited : 0 ≤ inherited)
    (k s : ℕ) (hk : 10 ≤ k) (hs : s ≤ k+1)
    (hq : q = 40*(k+1)) (hell : ell = t^(11/10 : ℝ))
    (hdelta : delta = t^k) (htau : tau = t^(6/5 : ℝ)) (hreserve : deltaNext = (t^(6/5 : ℝ))^s) :
    (deltaNext^2)⁻¹*C*(delta*(tau/ell)^q+delta^3/tau+
        (delta^2+delta)*(budget*(ell/t)^q+inherited*(tau/t)^q)) ≤
      (2*C*(1+budget))*t^(1/5 : ℝ)*(1+inherited) ∧
    (s = k+1 → (deltaNext^2)⁻¹*C*(delta*(tau/ell)^q+delta^3/tau+
        (delta^2+delta)*(budget*(ell/t)^q+inherited*(tau/t)^q)) =
      ∑ i : Fin 6, actualRepairSixCoefficients C budget inherited i*t^repairErrorExponent k i) := by
  rw [hq,hell,hdelta,htau,hreserve]
  refine ⟨actual_repair_six_recurrence_bound ht ht1 hC hbudget hinherited k s hk hs,?_⟩
  intro hsk
  rw [hsk]
  exact actual_repair_six_exact_exponents ht k C budget inherited

end GlobalEmbedding.Continuation
#print axioms GlobalEmbedding.Continuation.actual_repair_six_exact_exponents
#print axioms GlobalEmbedding.Continuation.actual_repair_six_normalized_bound
#print axioms GlobalEmbedding.Continuation.actual_repair_six_recurrence_bound
