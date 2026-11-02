import GlobalEmbedding.Paper.CollarCKCoefficientComparison
import GlobalEmbedding.Paper.CollarCKSpatialFormalSolution
import Mathlib.RingTheory.MvPowerSeries.Inverse
import Mathlib.Data.Finsupp.Weight

/-!
# Actual rational coefficient majorant for CK

Source: Gantumur, Math580 notes2, Theorem18, pp9–10.
DAG: `collar-ck-rational-coefficient-majorant`. Exclusive owner W4.
Only estimates on native formal series are introduced; the Goursat RHS is expanded literally.
-/

noncomputable section
open scoped BigOperators

namespace GlobalEmbedding.Paper

/-- The native formal inverse of `1-q` has nonnegative coefficients when `q` has
zero constant coefficient and nonnegative coefficients. The actual inverse recursion
strictly decreases total degree in every nonzero antidiagonal term. -/
theorem collarCK_inverse_nonneg {σ : Type*} (q : MvPowerSeries σ ℝ)
    (hq0 : MvPowerSeries.constantCoeff q = 0)
    (hq : ∀ d, 0 ≤ MvPowerSeries.coeff d q) :
    ∀ d, 0 ≤ MvPowerSeries.coeff d (1 - q)⁻¹ := by
  classical
  have hc : MvPowerSeries.constantCoeff (1 - q) = 1 := by simp [hq0]
  suffices ∀ N (d : σ →₀ ℕ), d.degree = N →
      0 ≤ MvPowerSeries.coeff d (1 - q)⁻¹ from fun d ↦ this _ d rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro d hd
    rw [MvPowerSeries.coeff_inv, hc]
    by_cases hd0 : d = 0
    · simp [hd0]
    simp only [hd0, ite_false, inv_one, neg_one_mul]
    apply neg_nonneg.mpr
    apply Finset.sum_nonpos
    intro x hx
    split_ifs with hxd
    · have hxsum : x.1 + x.2 = d := Finset.mem_antidiagonal.mp hx
      have hx1 : x.1 ≠ 0 := by
        intro h
        have : x.2 = d := by simpa [h] using hxsum
        exact (ne_of_lt hxd) this
      have hdeg1 : 0 < x.1.degree :=
        Nat.pos_of_ne_zero (fun h ↦ hx1 ((Finsupp.degree_eq_zero_iff _).mp h))
      have hdeg : x.2.degree < N := by
        have := congrArg Finsupp.degree hxsum
        simp only [map_add] at this
        omega
      have hcoeff : MvPowerSeries.coeff x.1 (1 - q) =
          -MvPowerSeries.coeff x.1 q := by simp [map_sub, MvPowerSeries.coeff_one, hx1]
      rw [hcoeff]
      exact mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr (hq _))
        (ih _ hdeg _ rfl)
    · exact le_rfl

/-- A selected positive convolution term bounds the next inverse coefficient. -/
theorem collarCK_inverse_coeff_step {σ : Type*} (q : MvPowerSeries σ ℝ)
    (hq0 : MvPowerSeries.constantCoeff q = 0)
    (hq : ∀ d, 0 ≤ MvPowerSeries.coeff d q) (d : σ →₀ ℕ) (i : σ) :
    MvPowerSeries.coeff (Finsupp.single i 1) q *
        MvPowerSeries.coeff d (1 - q)⁻¹ ≤
      MvPowerSeries.coeff (Finsupp.single i 1 + d) (1 - q)⁻¹ := by
  classical
  have hc : MvPowerSeries.constantCoeff (1 - q) ≠ 0 := by simp [hq0]
  have heq : (1 - q)⁻¹ = 1 + q * (1 - q)⁻¹ := by
    have h := MvPowerSeries.mul_inv_cancel (1 - q) hc
    rw [sub_mul, one_mul] at h
    exact sub_eq_iff_eq_add.mp h
  have hd : Finsupp.single i 1 + d ≠ 0 := by
    intro h
    have := congrArg (fun e : σ →₀ ℕ ↦ e i) h
    simp at this
  conv_rhs => rw [heq, map_add, MvPowerSeries.coeff_one, ite_eq_right hd, zero_add,
    MvPowerSeries.coeff_mul]
  exact Finset.single_le_sum
    (fun p _ ↦ mul_nonneg (hq p.1) (collarCK_inverse_nonneg q hq0 hq p.2))
    (Finset.mem_antidiagonal.mpr rfl :
      (Finsupp.single i 1, d) ∈ Finset.antidiagonal (Finsupp.single i 1 + d))

/-- Uniform lower bounds on the linear coefficients used by a monomial give a
geometric lower bound on that monomial's inverse coefficient. Coordinates absent
from the monomial require no positive linear coefficient. -/
theorem collarCK_inverse_geometric_lower {σ : Type*} (q : MvPowerSeries σ ℝ)
    (hq0 : MvPowerSeries.constantCoeff q = 0)
    (hq : ∀ d, 0 ≤ MvPowerSeries.coeff d q) (r : ℝ) (hr : 0 ≤ r) :
    ∀ d : σ →₀ ℕ, (∀ i ∈ d.support,
      r ≤ MvPowerSeries.coeff (Finsupp.single i 1) q) →
      r ^ d.degree ≤ MvPowerSeries.coeff d (1 - q)⁻¹ := by
  classical
  suffices ∀ N (d : σ →₀ ℕ), d.degree = N →
      (∀ i ∈ d.support, r ≤ MvPowerSeries.coeff (Finsupp.single i 1) q) →
      r ^ d.degree ≤ MvPowerSeries.coeff d (1 - q)⁻¹ from fun d ↦ this _ d rfl
  intro N
  induction N using Nat.strong_induction_on with
  | h N ih =>
    intro d hd hl
    by_cases hd0 : d = 0
    · simp [hd0, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hq0]
    obtain ⟨i, hi⟩ := Finsupp.support_nonempty_iff.mpr hd0
    have hdi : 1 ≤ d i := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hi)
    have hs : Finsupp.single i 1 ≤ d := Finsupp.single_le_iff.mpr hdi
    let e := d - Finsupp.single i 1
    have he : Finsupp.single i 1 + e = d := add_tsub_cancel_of_le hs
    have hdeg : 1 + e.degree = d.degree := by
      simpa only [map_add, Finsupp.degree_single] using congrArg Finsupp.degree he
    have hind : r ^ e.degree ≤ MvPowerSeries.coeff e (1 - q)⁻¹ := by
      apply ih e.degree (by omega) e rfl
      intro j hj
      apply hl j
      apply Finsupp.mem_support_iff.mpr
      have hle : e ≤ d := tsub_le_self
      have hpos : 0 < e j := Nat.pos_of_ne_zero (Finsupp.mem_support_iff.mp hj)
      exact Nat.ne_of_gt (hpos.trans_le (hle j))
    calc
      r ^ d.degree = r * r ^ e.degree := by rw [← hdeg, pow_add]; simp
      _ ≤ MvPowerSeries.coeff (Finsupp.single i 1) q *
          MvPowerSeries.coeff e (1 - q)⁻¹ :=
        mul_le_mul (hl i hi) hind (pow_nonneg hr _) (hq _)
      _ ≤ MvPowerSeries.coeff d (1 - q)⁻¹ := by
        simpa only [he] using collarCK_inverse_coeff_step q hq0 hq e i

/-- A two-block rational denominator has geometric coefficients as soon as each
coordinate occurs with sufficient weight in at least one of its two factors. -/
theorem collarCK_two_inverse_geometric_lower {σ : Type*}
    (q p : MvPowerSeries σ ℝ)
    (hq0 : MvPowerSeries.constantCoeff q = 0)
    (hp0 : MvPowerSeries.constantCoeff p = 0)
    (hq : ∀ d, 0 ≤ MvPowerSeries.coeff d q)
    (hp : ∀ d, 0 ≤ MvPowerSeries.coeff d p) (r : ℝ) (hr : 0 ≤ r)
    (hlinear : ∀ i, r ≤ MvPowerSeries.coeff (Finsupp.single i 1) q ∨
      r ≤ MvPowerSeries.coeff (Finsupp.single i 1) p) (d : σ →₀ ℕ) :
    r ^ d.degree ≤ MvPowerSeries.coeff d ((1 - q)⁻¹ * (1 - p)⁻¹) := by
  classical
  let P (i : σ) := r ≤ MvPowerSeries.coeff (Finsupp.single i 1) q
  let a := d.filter P
  let b := d.filter (fun i ↦ ¬P i)
  have hab : a + b = d := Finsupp.filter_add_filter_not d P
  have ha : r ^ a.degree ≤ MvPowerSeries.coeff a (1 - q)⁻¹ := by
    apply collarCK_inverse_geometric_lower q hq0 hq r hr
    intro i hi
    change i ∈ d.support.filter P at hi
    exact (Finset.mem_filter.mp hi).2
  have hb : r ^ b.degree ≤ MvPowerSeries.coeff b (1 - p)⁻¹ := by
    apply collarCK_inverse_geometric_lower p hp0 hp r hr
    intro i hi
    change i ∈ d.support.filter (fun i ↦ ¬P i) at hi
    exact (hlinear i).resolve_left (Finset.mem_filter.mp hi).2
  calc
    r ^ d.degree = r ^ a.degree * r ^ b.degree := by
      rw [← hab, map_add, pow_add]
    _ ≤ MvPowerSeries.coeff a (1 - q)⁻¹ * MvPowerSeries.coeff b (1 - p)⁻¹ :=
      mul_le_mul ha hb (pow_nonneg hr _) (collarCK_inverse_nonneg q hq0 hq _)
    _ ≤ MvPowerSeries.coeff d ((1 - q)⁻¹ * (1 - p)⁻¹) := by
      rw [MvPowerSeries.coeff_mul]
      exact Finset.single_le_sum
        (fun x _ ↦ mul_nonneg (collarCK_inverse_nonneg q hq0 hq x.1)
          (collarCK_inverse_nonneg p hp0 hp x.2))
        (Finset.mem_antidiagonal.mpr hab : (a, b) ∈ Finset.antidiagonal d)

/-- The actual positive-degree geometric RHS bound is dominated by the rational
two-factor majorant with its constant term removed. This changes no series carrier. -/
theorem collarCK_rational_rhs_domination {σ : Type*}
    (H q p : MvPowerSeries σ ℝ) (M R : ℝ) (hM : 0 ≤ M) (hR : 0 < R)
    (hH0 : MvPowerSeries.constantCoeff H = 0)
    (hH : ∀ d, |MvPowerSeries.coeff d H| ≤ M / R ^ d.degree)
    (hq0 : MvPowerSeries.constantCoeff q = 0)
    (hp0 : MvPowerSeries.constantCoeff p = 0)
    (hq : ∀ d, 0 ≤ MvPowerSeries.coeff d q)
    (hp : ∀ d, 0 ≤ MvPowerSeries.coeff d p)
    (hlinear : ∀ i, R⁻¹ ≤ MvPowerSeries.coeff (Finsupp.single i 1) q ∨
      R⁻¹ ≤ MvPowerSeries.coeff (Finsupp.single i 1) p) :
    CollarCKCoeffDominated H (M • ((1 - q)⁻¹ * (1 - p)⁻¹ - 1)) := by
  classical
  intro d
  by_cases hd : d = 0
  · simp [hd, MvPowerSeries.coeff_zero_eq_constantCoeff_apply, hH0, hq0, hp0]
  · simp only [map_smul, smul_eq_mul, map_sub, MvPowerSeries.coeff_one,
      ite_eq_right hd, sub_zero]
    calc
      |MvPowerSeries.coeff d H| ≤ M / R ^ d.degree := hH d
      _ = M * (R⁻¹) ^ d.degree := by rw [div_eq_mul_inv, inv_pow]
      _ ≤ M * MvPowerSeries.coeff d ((1 - q)⁻¹ * (1 - p)⁻¹) :=
        mul_le_mul_of_nonneg_left
          (collarCK_two_inverse_geometric_lower q p hq0 hp0 hq hp R⁻¹
            (inv_nonneg.mpr hR.le) hlinear d) hM

/-- The expanded SAME Goursat rational RHS dominates every normalized RHS with
the actual geometric coefficient estimate. The time weight uses exactly `rho≤1`.
This theorem introduces no separate rational-RHS definition. -/
theorem collarCK_goursat_rhs_domination {n m : ℕ}
    (H : MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ) (M R rho : ℝ)
    (hM : 0 ≤ M) (hR : 0 < R) (hrho : 0 < rho) (hrho1 : rho ≤ 1)
    (hH0 : MvPowerSeries.constantCoeff H = 0)
    (hH : ∀ d, |MvPowerSeries.coeff d H| ≤ M / R ^ d.degree) :
    CollarCKCoeffDominated H
      (M • (((1 - R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inl i)) +
          rho⁻¹ • MvPowerSeries.X (Sum.inr (Sum.inl ())) +
          (∑ j : Fin m, MvPowerSeries.X (Sum.inr (Sum.inr (Sum.inl j))))))⁻¹) *
        ((1 - R⁻¹ • (∑ i : Fin n, ∑ j : Fin m,
          MvPowerSeries.X (Sum.inr (Sum.inr (Sum.inr (i, j))))))⁻¹) - 1)) := by
  classical
  let q : MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ :=
    R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inl i)) +
      rho⁻¹ • MvPowerSeries.X (Sum.inr (Sum.inl ())) +
      (∑ j : Fin m, MvPowerSeries.X (Sum.inr (Sum.inr (Sum.inl j)))))
  let p : MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ :=
    R⁻¹ • (∑ i : Fin n, ∑ j : Fin m,
      MvPowerSeries.X (Sum.inr (Sum.inr (Sum.inr (i, j)))))
  have hX (d : (Fin n ⊕ CollarCKSlot n m) →₀ ℕ)
      (i : Fin n ⊕ CollarCKSlot n m) :
      0 ≤ MvPowerSeries.coeff d (MvPowerSeries.X i : MvPowerSeries _ ℝ) := by
    rw [MvPowerSeries.coeff_X]
    split_ifs <;> norm_num
  apply collarCK_rational_rhs_domination H q p M R hM hR hH0 hH
  · simp [q]
  · simp [p]
  · intro d
    simp only [q, map_smul, smul_eq_mul, map_add, map_sum]
    exact mul_nonneg (inv_nonneg.mpr hR.le)
      (add_nonneg (add_nonneg (Finset.sum_nonneg (fun i _ ↦ hX d _))
        (mul_nonneg (inv_nonneg.mpr hrho.le) (hX d _)))
        (Finset.sum_nonneg (fun j _ ↦ hX d _)))
  · intro d
    simp only [p, map_smul, smul_eq_mul, map_sum]
    exact mul_nonneg (inv_nonneg.mpr hR.le)
      (Finset.sum_nonneg (fun i _ ↦ Finset.sum_nonneg (fun j _ ↦ hX d _)))
  · intro i
    rcases i with i | (⟨⟩ | (j | ⟨i, j⟩))
    · left
      simp [q, MvPowerSeries.coeff_index_single_X]
    · left
      simp only [q, map_smul, smul_eq_mul, map_add, map_sum,
        MvPowerSeries.coeff_index_single_X]
      simp only [Sum.inr.injEq, Sum.inl_ne_inr, Sum.inr_ne_inl, ite_false,
        Finset.sum_const_zero, ite_true, mul_one, zero_add, add_zero]
      exact le_mul_of_one_le_right (inv_nonneg.mpr hR.le) ((one_le_inv₀ hrho).mpr hrho1)
    · left
      simp [q, MvPowerSeries.coeff_index_single_X]
    · right
      simp [p, MvPowerSeries.coeff_index_single_X, Prod.mk.injEq, ite_and]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCK_inverse_nonneg
#print axioms GlobalEmbedding.Paper.collarCK_inverse_coeff_step
#print axioms GlobalEmbedding.Paper.collarCK_inverse_geometric_lower
#print axioms GlobalEmbedding.Paper.collarCK_two_inverse_geometric_lower
#print axioms GlobalEmbedding.Paper.collarCK_rational_rhs_domination
#print axioms GlobalEmbedding.Paper.collarCK_goursat_rhs_domination
