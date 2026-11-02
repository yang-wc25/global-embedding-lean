import Mathlib.RingTheory.PowerSeries.Substitution

open PowerSeries

/-!
# Actual coefficient causality of formal nonlinear substitution

Source: Gantumur, notes2, Theorem18 formal normal-variable coefficient recursion.
-/

namespace GlobalEmbedding.Paper

/-- The kth coefficient of actual multivariate substitution into the single normal variable
uses only the input coefficients through k.

Source: Gantumur, notes2, Theorem18 proof, lines787–814, coefficient dependency at802.
The coefficient ring can itself be a ring of formal spatial series. Finite source variables
and zero constant coefficients ensure both substitutions satisfy native HasSubst, so neither
side is the default value assigned to an inadmissible substitution.

Proof: agreement of the univariate input coefficients through k gives equality of their total
truncations at k+1. The native exact truncation/substitution theorem replaces each input by
that truncation while preserving the output truncation. Equal truncated inputs therefore give
equal output truncations, whose actual kth coefficients are the claimed coefficients.
This is a formal algebraic causality theorem only; no convergence or analytic PDE is asserted. -/
theorem collarCKFormalSubstitutionCausality {σ A : Type*} [Finite σ] [CommRing A]
    (G : MvPowerSeries σ A) (p q : σ → PowerSeries A)
    (hp : ∀ i, constantCoeff (p i) = 0) (hq : ∀ i, constantCoeff (q i) = 0)
    (k : ℕ) (hprefix : ∀ i j, j ≤ k → coeff j (p i) = coeff j (q i)) :
    coeff k (MvPowerSeries.subst p G) = coeff k (MvPowerSeries.subst q G) := by
  have htrunc (i : σ) : MvPowerSeries.truncTotal (k + 1) (p i) =
      MvPowerSeries.truncTotal (k + 1) (q i) := by
    ext d
    by_cases hd : d.degree < k + 1
    · rw [MvPowerSeries.coeff_truncTotal _ hd, MvPowerSeries.coeff_truncTotal _ hd]
      have hdeg : d.degree = d () := by
        conv_lhs => rw [Finsupp.unique_single d, Finsupp.degree_single]
      rw [← PowerSeries.coeff_def (s := d) rfl]
      exact hprefix i (d ()) (by omega)
    · rw [MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega),
        MvPowerSeries.coeff_truncTotal_eq_zero _ (by omega)]
  have hout : MvPowerSeries.truncTotal (k + 1) (MvPowerSeries.subst p G) =
      MvPowerSeries.truncTotal (k + 1) (MvPowerSeries.subst q G) := by
    rw [MvPowerSeries.truncTotal_subst hp, MvPowerSeries.truncTotal_subst hq]
    simp only [htrunc]
  have hcoeff := congrArg (fun f : MvPolynomial Unit A ↦ f.coeff (Finsupp.single () k)) hout
  rw [MvPowerSeries.coeff_truncTotal _ (by simp),
    MvPowerSeries.coeff_truncTotal _ (by simp)] at hcoeff
  exact hcoeff

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKFormalSubstitutionCausality
