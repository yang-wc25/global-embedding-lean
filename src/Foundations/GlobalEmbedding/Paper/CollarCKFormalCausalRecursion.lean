import Mathlib.RingTheory.PowerSeries.Derivative
import Mathlib.Algebra.Algebra.Rat

open PowerSeries

/-!
# Actual formal normal-variable recursion for coefficient-causal vector fields

Source: Gantumur, Math580 notes2, Theorem18 formal coefficient recursion, lines787–814.
This is a formal-series theorem only; original-PDE substitution causality and convergence
remain separate obligations.
-/

namespace GlobalEmbedding.Paper

variable {A : Type*} [CommRing A] [Algebra ℚ A]

private noncomputable def partialFormal (F : PowerSeries A → PowerSeries A) (a₀ : A) :
    ℕ → PowerSeries A
  | 0 => C a₀
  | n + 1 => partialFormal F a₀ n +
      monomial (n + 1) ((n + 1 : ℚ)⁻¹ • coeff n (F (partialFormal F a₀ n)))

private theorem partialFormal_high (F : PowerSeries A → PowerSeries A) (a₀ : A)
    (n k : ℕ) (hk : n < k) : coeff k (partialFormal F a₀ n) = 0 := by
  induction n with
  | zero => simp only [partialFormal, coeff_C, ite_eq_right (by omega : k ≠ 0)]
  | succ n ih =>
    rw [partialFormal, map_add, ih (by omega), coeff_monomial,
      ite_eq_right (by omega : k ≠ n + 1), add_zero]

private theorem partialFormal_stable (F : PowerSeries A → PowerSeries A) (a₀ : A)
    (n k : ℕ) (hnk : n ≤ k) :
    coeff n (partialFormal F a₀ k) = coeff n (partialFormal F a₀ n) := by
  refine Nat.le_induction rfl (fun k hk ih ↦ ?_) k hnk
  rw [partialFormal, map_add, coeff_monomial, ite_eq_right (by omega : n ≠ k + 1), add_zero, ih]

private noncomputable def formalCandidate (F : PowerSeries A → PowerSeries A) (a₀ : A) :
    PowerSeries A := mk fun n ↦ coeff n (partialFormal F a₀ n)

private theorem formalCandidate_prefix (F : PowerSeries A → PowerSeries A) (a₀ : A)
    (n k : ℕ) (hnk : n ≤ k) :
    coeff n (formalCandidate F a₀) = coeff n (partialFormal F a₀ k) := by
  rw [formalCandidate, coeff_mk]
  exact (partialFormal_stable F a₀ n k hnk).symm

private theorem formalCandidate_next (F : PowerSeries A → PowerSeries A) (a₀ : A)
    (n : ℕ) : coeff (n + 1) (formalCandidate F a₀) =
      (n + 1 : ℚ)⁻¹ • coeff n (F (partialFormal F a₀ n)) := by
  rw [formalCandidate, coeff_mk, partialFormal, map_add,
    partialFormal_high F a₀ n (n + 1) (by omega), coeff_monomial_same, zero_add]

private theorem rational_cancel (n : ℕ) (a : A) :
    ((n + 1 : ℚ)⁻¹ • a) * (n + 1 : A) = a := by
  have hcast : (n + 1 : A) = algebraMap ℚ A (n + 1 : ℚ) := by simp
  rw [hcast, mul_comm, ← Algebra.smul_def, smul_smul]
  rw [mul_inv_cancel₀ (by positivity : (n + 1 : ℚ) ≠ 0), one_smul]

/-- Every coefficient-causal formal vector field over a commutative rational algebra has a
unique formal solution through each initial coefficient.

Source: the normal-variable coefficient recursion in Gantumur, notes2, Theorem18, lines787–814.
The hypothesis says precisely that the kth output coefficient uses input coefficients only
through k. It does not assume any solution, analyticity or convergence. The coefficient algebra
may itself be a finite product of rings of formal spatial power series.

Proof: start with the actual constant series P₀=C(a₀), and adjoin at step k the monomial of
degree k+1 with coefficient coeffₖ(F(Pₖ))/(k+1), using rational scalar multiplication.
All coefficients through k are unchanged by this step. Define u coefficient n as coefficient n
of Pₙ. Stabilization proves u and Pₖ agree through k, so causality identifies the kth coefficient
of F(u) with that of F(Pₖ). The actual formal derivative coefficient formula and rational
cancellation give u′=F(u). Strong induction and the same causality determine the coefficients
of any competitor uniquely. Applying this to the original CK equation still requires proving
the actual spatial-derivative/substitution operator is causal, and convergence requires the
separate coefficientwise majorant domination theorem. -/
theorem collarCKFormalCausalRecursion (F : PowerSeries A → PowerSeries A) (a₀ : A)
    (hF : ∀ p q k, (∀ j ≤ k, coeff j p = coeff j q) →
      coeff k (F p) = coeff k (F q)) :
    ∃! u : PowerSeries A, constantCoeff u = a₀ ∧ derivative u = F u := by
  let u := formalCandidate F a₀
  have hu0 : constantCoeff u = a₀ := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    simp only [u, formalCandidate, coeff_mk, partialFormal, coeff_zero_C]
  have hdu : derivative u = F u := by
    ext n
    rw [coeff_derivative, formalCandidate_next, rational_cancel]
    exact hF (partialFormal F a₀ n) u n
      (fun j hj ↦ (formalCandidate_prefix F a₀ j n hj).symm)
  refine ⟨u, ⟨hu0, hdu⟩, ?_⟩
  rintro v ⟨hv0, hdv⟩
  apply PowerSeries.ext
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    cases n with
    | zero => simpa only [coeff_zero_eq_constantCoeff_apply, hu0] using hv0
    | succ n =>
      have heq : coeff (n + 1) v * (n + 1 : ℕ) =
          coeff (n + 1) u * (n + 1 : ℕ) := by
        simp only [Nat.cast_add, Nat.cast_one]
        rw [← coeff_derivative, ← coeff_derivative, hdv, hdu]
        exact hF v u n (fun j hj ↦ ih j (by omega))
      have hunit : IsUnit ((n + 1 : ℕ) : A) := by
        have hq : IsUnit (n + 1 : ℚ) := isUnit_iff_ne_zero.mpr (by positivity)
        simpa only [map_add, map_natCast, map_one, Nat.cast_add, Nat.cast_one] using
          hq.map (algebraMap ℚ A)
      exact hunit.mul_right_cancel heq

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKFormalCausalRecursion
