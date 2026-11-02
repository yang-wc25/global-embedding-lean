import Mathlib.RingTheory.MvPowerSeries.Substitution
import Mathlib.RingTheory.MvPowerSeries.Derivative
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Basic.Real.Basic

/-!
# Genuine coefficient comparison for the CK majorant argument

Source: Gantumur, Math580 notes2, Theorem18, printed pp9–10.
DAG: `collar-ck-coefficient-comparison`. Exclusive owner W4.
All operators below are the existing Mathlib formal series operators.
-/
noncomputable section
open scoped BigOperators

namespace GlobalEmbedding.Paper

/-- Absolute coefficient domination on the existing real multivariate series ring. -/
def CollarCKCoeffDominated {Idx : Type*} (f F : MvPowerSeries Idx ℝ) : Prop :=
  ∀ d, |MvPowerSeries.coeff d f| ≤ MvPowerSeries.coeff d F

namespace CollarCKCoeffDominated

variable {Idx : Type*} {f F g G : MvPowerSeries Idx ℝ}

/-- Actual domination implies nonnegativity of every dominating coefficient. -/
theorem nonneg (hf : CollarCKCoeffDominated f F) (d : Idx →₀ ℕ) :
    0 ≤ MvPowerSeries.coeff d F := (abs_nonneg _).trans (hf d)

/-- The actual unit series dominates itself, including its zero higher coefficients. -/
theorem one : CollarCKCoeffDominated (1 : MvPowerSeries Idx ℝ) 1 := by
  classical
  intro d
  simp only [MvPowerSeries.coeff_one]
  split_ifs <;> simp

/-- The triangle inequality compares the actual coefficient of a sum. -/
theorem add (hf : CollarCKCoeffDominated f F) (hg : CollarCKCoeffDominated g G) :
    CollarCKCoeffDominated (f + g) (F + G) := by
  intro d
  simp only [map_add]
  exact (abs_add_le _ _).trans (add_le_add (hf d) (hg d))

/-- The true finite antidiagonal convolution preserves coefficient domination. -/
theorem mul (hf : CollarCKCoeffDominated f F) (hg : CollarCKCoeffDominated g G) :
    CollarCKCoeffDominated (f * g) (F * G) := by
  classical
  intro d
  rw [MvPowerSeries.coeff_mul, MvPowerSeries.coeff_mul]
  calc
    |∑ p ∈ Finset.antidiagonal d,
        MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g| ≤
      ∑ p ∈ Finset.antidiagonal d,
        |MvPowerSeries.coeff p.1 f * MvPowerSeries.coeff p.2 g| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ p ∈ Finset.antidiagonal d,
        MvPowerSeries.coeff p.1 F * MvPowerSeries.coeff p.2 G := by
      apply Finset.sum_le_sum
      intro p _
      rw [abs_mul]
      exact mul_le_mul (hf p.1) (hg p.2) (abs_nonneg _) (hf.nonneg _)

/-- Powers, including exponent zero, use the actual multiplication comparison. -/
theorem pow (hf : CollarCKCoeffDominated f F) (k : ℕ) :
    CollarCKCoeffDominated (f ^ k) (F ^ k) := by
  induction k with
  | zero => simpa only [pow_zero] using (one (Idx := Idx))
  | succ k ih => simpa only [pow_succ] using ih.mul hf

/-- Every genuine finite product preserves the common coefficient comparison. -/
theorem prod {J : Type*} (s : Finset J) (a A : J → MvPowerSeries Idx ℝ)
    (h : ∀ j ∈ s, CollarCKCoeffDominated (a j) (A j)) :
    CollarCKCoeffDominated (∏ j ∈ s, a j) (∏ j ∈ s, A j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (one (Idx := Idx))
  | @insert j s hj ih =>
    simp only [Finset.prod_insert hj]
    exact (h j (by simp)).mul (ih (fun k hk ↦ h k (by simp [hk])))

/-- Spatial differentiation shifts the actual coefficient and multiplies by a nonnegative
integer. This uses no claim that spatial differentiation lowers the induction order. -/
theorem pderiv (hf : CollarCKCoeffDominated f F) (i : Idx) :
    CollarCKCoeffDominated (MvPowerSeries.pderiv i f) (MvPowerSeries.pderiv i F) := by
  intro d
  rw [MvPowerSeries.coeff_pderiv, MvPowerSeries.coeff_pderiv, abs_mul,
    abs_of_nonneg (by positivity : (0 : ℝ) ≤ (d i : ℝ) + 1)]
  exact mul_le_mul_of_nonneg_right (hf _) (by positivity)

/-- Lawful nonlinear substitution preserves absolute coefficient domination.
Each actual coefficient is a finite sum by native HasSubst. Expand both supports into the
same finite union, then use product comparison and the triangle inequality. In the CK use,
these are full multivariate total-origin substitutions; the scalar majorant is never required
to have zero normal-constant spatial series. -/
theorem subst {Src : Type*} {f F : MvPowerSeries Src ℝ}
    (hf : CollarCKCoeffDominated f F)
    (a A : Src → MvPowerSeries Idx ℝ)
    (ha : MvPowerSeries.HasSubst a) (hA : MvPowerSeries.HasSubst A)
    (h : ∀ i, CollarCKCoeffDominated (a i) (A i)) :
    CollarCKCoeffDominated (MvPowerSeries.subst a f) (MvPowerSeries.subst A F) := by
  classical
  intro e
  have hprod (d : Src →₀ ℕ) :
      CollarCKCoeffDominated (d.prod fun i k ↦ a i ^ k) (d.prod fun i k ↦ A i ^ k) := by
    exact prod d.support _ _ (fun i _ ↦ (h i).pow (d i))
  let u (d : Src →₀ ℕ) :=
    MvPowerSeries.coeff d f * MvPowerSeries.coeff e (d.prod fun i k ↦ a i ^ k)
  let v (d : Src →₀ ℕ) :=
    MvPowerSeries.coeff d F * MvPowerSeries.coeff e (d.prod fun i k ↦ A i ^ k)
  have hu : u.HasFiniteSupport := MvPowerSeries.coeff_subst_finite ha f e
  have hv : v.HasFiniteSupport := MvPowerSeries.coeff_subst_finite hA F e
  let s := (hu.union hv).toFinset
  have hus : Function.support u ⊆ (s : Set (Src →₀ ℕ)) := by
    intro d hd
    exact (hu.union hv).mem_toFinset.mpr (Or.inl hd)
  have hvs : Function.support v ⊆ (s : Set (Src →₀ ℕ)) := by
    intro d hd
    exact (hu.union hv).mem_toFinset.mpr (Or.inr hd)
  rw [MvPowerSeries.coeff_subst ha, MvPowerSeries.coeff_subst hA]
  change |finsum u| ≤ finsum v
  rw [finsum_eq_finsetSum_of_support_subset u hus, finsum_eq_finsetSum_of_support_subset v hvs]
  calc
    |∑ d ∈ s, u d| ≤ ∑ d ∈ s, |u d| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ d ∈ s, v d := by
      apply Finset.sum_le_sum
      intro d _
      dsimp only [u, v]
      rw [abs_mul]
      exact mul_le_mul (hf d) (hprod d e) (abs_nonneg _) (hf.nonneg _)

end CollarCKCoeffDominated

#print axioms CollarCKCoeffDominated
#print axioms CollarCKCoeffDominated.nonneg
#print axioms CollarCKCoeffDominated.one
#print axioms CollarCKCoeffDominated.add
#print axioms CollarCKCoeffDominated.mul
#print axioms CollarCKCoeffDominated.pow
#print axioms CollarCKCoeffDominated.prod
#print axioms CollarCKCoeffDominated.pderiv
#print axioms CollarCKCoeffDominated.subst

end GlobalEmbedding.Paper
