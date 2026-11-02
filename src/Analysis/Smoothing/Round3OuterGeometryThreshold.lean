import Smoothing.ParameterRound2RepairScales

/-! A single finite scalar entrance for the ACTUAL repair scales. The
threshold is chosen from fixed low-order smoothing/reference/linear costs,
then works for either next reserve and every later scale below it. It supplies
the exact two smallness conditions consumed by the computed positive target
and fixed-reference C2 stability, without any current-SF compact choice.
-/
noncomputable section
open GlobalEmbedding.Paper GlobalEmbedding.Offline Set Function
open scoped ContDiff
namespace GlobalEmbedding.Continuation

theorem round3_repair_literal_low_powers {t : ℝ} (ht : 0 < t) (ht1 : t ≤ 1)
    (k s : ℕ) (hk : 10 ≤ k) (hks : k ≤ s) :
    (t^(11/10 : ℝ)/t)^(40*(k+1)) ≤ t ∧
    ((t^(6/5 : ℝ))^s/t^k)^2 ≤ t := by
  constructor
  · rw [(parameterRound2_repair_smoothing_powers ht k).1]
    simpa only [pow_one] using pow_le_pow_of_le_one ht.le ht1 (by omega : 1 ≤ 4*(k+1))
  · rw [div_pow,repair_reserve_square ht,← pow_mul,
      ← Real.rpow_natCast t (k*2),← Real.rpow_sub ht]
    apply Real.rpow_le_self_of_le_one ht.le ht1
    have hk' : (10 : ℝ) ≤ k := by exact_mod_cast hk
    have hs' : (k : ℝ) ≤ s := by exact_mod_cast hks
    push_cast
    linarith

def round3RepairComputedGeometryThreshold (C budget reference L rho epsilon : ℝ) : ℝ :=
  min 1 (min (epsilon/(2*(C*budget+1)))
    (rho/(4*(L+1)*(C*budget+reference+1))))

theorem round3RepairComputedGeometryThreshold_pos
    (C budget reference L rho epsilon : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ budget) (hRef : 0 ≤ reference) (hL : 0 ≤ L)
    (hrho : 0 < rho) (heps : 0 < epsilon) :
    0 < round3RepairComputedGeometryThreshold C budget reference L rho epsilon := by
  unfold round3RepairComputedGeometryThreshold
  positivity

/-- The same literal tail and reserve satisfy both geometric entrances.
There are no high-order target norms in this threshold. -/
theorem round3_repair_literal_geometry_threshold
    (C budget reference L rho epsilon : ℝ)
    (hC : 0 ≤ C) (hB : 0 ≤ budget) (hRef : 0 ≤ reference) (hL : 0 ≤ L)
    (hrho : 0 < rho) (heps : 0 < epsilon)
    (k s : ℕ) (hk : 10 ≤ k) (hks : k ≤ s)
    (t inherited mapInherited : ℝ) (ht : 0 < t)
    (htSmall : t ≤ round3RepairComputedGeometryThreshold C budget reference L rho epsilon)
    (hInherited : inherited ≤ rho/(4*(L+1)))
    (hMap : mapInherited ≤ epsilon/2) :
    t ≤ 1 ∧ ((t^(6/5 : ℝ))^s/t^k)^2 ≤ 1 ∧
    C*budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+mapInherited ≤ epsilon ∧
    L*(C*budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+inherited+
      ((t^(6/5 : ℝ))^s/t^k)^2*reference) ≤ rho/2 := by
  have hCB : 0 ≤ C*budget := mul_nonneg hC hB
  have ht1 : t ≤ 1 := htSmall.trans (min_le_left _ _)
  have htA : t ≤ epsilon/(2*(C*budget+1)) :=
    htSmall.trans ((min_le_right _ _).trans (min_le_left _ _))
  have htB : t ≤ rho/(4*(L+1)*(C*budget+reference+1)) :=
    htSmall.trans ((min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨hTail,hReserve⟩ := round3_repair_literal_low_powers ht ht1 k s hk hks
  have hCBt : C*budget*t ≤ epsilon/2 := by
    calc
      _ ≤ (C*budget+1)*t := mul_le_mul_of_nonneg_right (by linarith) ht.le
      _ ≤ (C*budget+1)*(epsilon/(2*(C*budget+1))) :=
        mul_le_mul_of_nonneg_left htA (by positivity)
      _ = epsilon/2 := by field_simp
  have hLTail : L*((C*budget+reference)*t) ≤ rho/4 := by
    have hd : 0 < (L+1)*(C*budget+reference+1) := mul_pos (by positivity) (by positivity)
    calc
      _ = (L*(C*budget+reference))*t := by ring
      _ ≤ ((L+1)*(C*budget+reference+1))*t :=
        mul_le_mul_of_nonneg_right (mul_le_mul (by linarith) (by linarith)
          (by positivity) (by positivity)) ht.le
      _ ≤ ((L+1)*(C*budget+reference+1))*(rho/(4*(L+1)*(C*budget+reference+1))) :=
        mul_le_mul_of_nonneg_left htB hd.le
      _ = rho/4 := by field_simp
  have hLInherited : L*inherited ≤ rho/4 := by
    calc
      _ ≤ L*(rho/(4*(L+1))) := mul_le_mul_of_nonneg_left hInherited hL
      _ ≤ (L+1)*(rho/(4*(L+1))) :=
        mul_le_mul_of_nonneg_right (by linarith) (by positivity)
      _ = rho/4 := by field_simp
  refine ⟨ht1,hReserve.trans ht1,?_,?_⟩
  · have h := add_le_add ((mul_le_mul_of_nonneg_left hTail hCB).trans hCBt) hMap
    linarith
  · have hInside : C*budget*(t^(11/10 : ℝ)/t)^(40*(k+1))+inherited+
        ((t^(6/5 : ℝ))^s/t^k)^2*reference ≤ (C*budget+reference)*t+inherited := by
      calc
        _ ≤ C*budget*t+inherited+t*reference :=
          add_le_add (add_le_add (mul_le_mul_of_nonneg_left hTail hCB) le_rfl)
            (mul_le_mul_of_nonneg_right hReserve hRef)
        _ = _ := by ring
    calc
      _ ≤ L*((C*budget+reference)*t+inherited) := mul_le_mul_of_nonneg_left hInside hL
      _ = L*((C*budget+reference)*t)+L*inherited := by ring
      _ ≤ rho/4+rho/4 := add_le_add hLTail hLInherited
      _ = rho/2 := by ring

#print axioms round3_repair_literal_low_powers
#print axioms round3_repair_literal_geometry_threshold
end GlobalEmbedding.Continuation
