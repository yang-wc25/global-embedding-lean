import GlobalEmbedding.Paper.CollarCKSpatialFormalSolution
import Mathlib.RingTheory.MvPowerSeries.Inverse

/-!
# The same formal Goursat RHS and its actual majorant slots

Source: Gantumur, notes2, Theorem 18, equations 47–51.
The expression is literally the one in the accepted W4 coefficient-majorant interface.
Only native formal series and full total-origin substitution are used. A majorant with
nonzero pure-spatial initial series is allowed throughout.
-/

noncomputable section
open scoped BigOperators
namespace GlobalEmbedding.Paper

/-- The sole full-input rational Goursat RHS, with all spatial/value/jet variables retained.
Source: Gantumur, Theorem 18, and W4's exact rational coefficient-majorant expression. -/
def collarCKGoursatRHS (n m : ℕ) (M R rho : ℝ) :
    MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ :=
  M • (((1 - R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inl i)) +
      rho⁻¹ • MvPowerSeries.X (Sum.inr (Sum.inl ())) +
      (∑ j : Fin m, MvPowerSeries.X (Sum.inr (Sum.inr (Sum.inl j))))))⁻¹) *
    ((1 - R⁻¹ • (∑ i : Fin n, ∑ j : Fin m,
      MvPowerSeries.X (Sum.inr (Sum.inr (Sum.inr (i, j))))))⁻¹) - 1)

/-- Actual symmetric-majorant slots, all using the same scalar series and its native derivatives.
Source: Gantumur, Theorem 18, symmetric component substitution. -/
def collarCKGoursatSlots {n m : ℕ} (u : MvPowerSeries (CollarCKFullIndex n) ℝ) :
    Fin n ⊕ CollarCKSlot n m → MvPowerSeries (CollarCKFullIndex n) ℝ
  | Sum.inl i => MvPowerSeries.X (Sum.inr i)
  | Sum.inr (Sum.inl _) => MvPowerSeries.X (Sum.inl ())
  | Sum.inr (Sum.inr (Sum.inl _)) => u
  | Sum.inr (Sum.inr (Sum.inr (i, _))) => MvPowerSeries.pderiv (Sum.inr i) u

/-- Origin and first-jet vanishing make every actual majorant slot have total constant zero.
Source: Gantumur, Theorem 18. The native derivative coefficient formula uses exactly one
coordinate singleton; no entire zero-normal spatial series is assumed. -/
theorem collarCKGoursatSlots_constantCoeff {n m : ℕ}
    (u : MvPowerSeries (CollarCKFullIndex n) ℝ)
    (h0 : MvPowerSeries.constantCoeff u = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) u = 0)
    (a : Fin n ⊕ CollarCKSlot n m) :
    MvPowerSeries.constantCoeff (collarCKGoursatSlots u a) = 0 := by
  rcases a with i | (⟨⟩ | (j | ⟨i, j⟩))
  · simp [collarCKGoursatSlots]
  · simp [collarCKGoursatSlots]
  · exact h0
  · rw [collarCKGoursatSlots, ← MvPowerSeries.coeff_zero_eq_constantCoeff_apply,
      MvPowerSeries.coeff_pderiv]
    simp [h1]

/-- The same actual majorant slots admit lawful full multivariate substitution.
Source: Gantumur, Theorem 18. Apply the native finite-variable zero-constant criterion. -/
theorem collarCKGoursatSlots_hasSubst {n m : ℕ}
    (u : MvPowerSeries (CollarCKFullIndex n) ℝ)
    (h0 : MvPowerSeries.constantCoeff u = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) u = 0) :
    MvPowerSeries.HasSubst (collarCKGoursatSlots (m := m) u) :=
  MvPowerSeries.hasSubst_of_constantCoeff_zero (collarCKGoursatSlots_constantCoeff u h0 h1)

/-- Substitution of the actual same-majorant slots gives the literal rational PDE expression.
Source: Gantumur, Theorem 18, symmetric majorant substitution.
Use the native substitution algebra homomorphism. The image of a source denominator has
constant one, so the image of its inverse is its unique native inverse. Expand the finite
spatial, value and derivative sums. This is lawful full-origin substitution throughout. -/
theorem collarCKGoursatRHS_subst {n m : ℕ} (M R rho : ℝ)
    (u : MvPowerSeries (CollarCKFullIndex n) ℝ)
    (h0 : MvPowerSeries.constantCoeff u = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) u = 0) :
    MvPowerSeries.subst (collarCKGoursatSlots u) (collarCKGoursatRHS n m M R rho) =
      M • (((1 - R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inr i)) +
          rho⁻¹ • MvPowerSeries.X (Sum.inl ()) + (∑ _j : Fin m, u)))⁻¹) *
        ((1 - R⁻¹ • (∑ i : Fin n, ∑ _j : Fin m,
          MvPowerSeries.pderiv (Sum.inr i) u))⁻¹) - 1) := by
  classical
  have ha := collarCKGoursatSlots_hasSubst (m := m) u h0 h1
  let Φ := MvPowerSeries.substAlgHom (R := ℝ) ha
  have hinverse (q : MvPowerSeries (Fin n ⊕ CollarCKSlot n m) ℝ)
      (hq0 : MvPowerSeries.constantCoeff q = 0) :
      Φ ((1 - q)⁻¹) = (1 - Φ q)⁻¹ := by
    have hz : MvPowerSeries.constantCoeff (Φ q) = 0 := by
      simpa only [Φ, MvPowerSeries.substAlgHom_apply] using
        MvPowerSeries.constantCoeff_subst_eq_zero ha
          (collarCKGoursatSlots_constantCoeff u h0 h1) hq0
    apply (MvPowerSeries.eq_inv_iff_mul_eq_one (by simp [hz])).mpr
    calc
      Φ ((1 - q)⁻¹) * (1 - Φ q) = Φ ((1 - q)⁻¹ * (1 - q)) := by
        rw [map_mul, map_sub, map_one]
      _ = 1 := by rw [MvPowerSeries.inv_mul_cancel _ (by simp [hq0]), map_one]
  rw [← MvPowerSeries.substAlgHom_apply ha]
  change Φ (collarCKGoursatRHS n m M R rho) = _
  unfold collarCKGoursatRHS
  rw [map_smul, map_sub, map_mul, map_one, hinverse _ (by simp), hinverse _ (by simp)]
  simp only [Φ, map_smul, map_add, map_sum, MvPowerSeries.substAlgHom_X,
    collarCKGoursatSlots]

/-- The exact rational formal PDE is equivalent to its denominator-cleared polynomial identity.
Source: Gantumur, Theorem 18. Both denominators have constant one by the genuine origin and
first jet. Apply native inverse cancellation to their product; this allows the actual analytic
PDE to be transported using product and derivative Taylor identities alone. -/
theorem collarCKGoursatRHS_equation_iff {n m : ℕ} (M R rho : ℝ)
    (u : MvPowerSeries (CollarCKFullIndex n) ℝ)
    (h0 : MvPowerSeries.constantCoeff u = 0)
    (h1 : ∀ i, MvPowerSeries.coeff (Finsupp.single i 1) u = 0) :
    (MvPowerSeries.pderiv (Sum.inl ()) u =
      MvPowerSeries.subst (collarCKGoursatSlots u) (collarCKGoursatRHS n m M R rho)) ↔
    ((MvPowerSeries.pderiv (Sum.inl ()) u + MvPowerSeries.C M) *
      (1 - R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inr i)) +
        rho⁻¹ • MvPowerSeries.X (Sum.inl ()) + (∑ _j : Fin m, u))) *
      (1 - R⁻¹ • (∑ i : Fin n, ∑ _j : Fin m,
        MvPowerSeries.pderiv (Sum.inr i) u)) = MvPowerSeries.C M) := by
  classical
  let A : MvPowerSeries (CollarCKFullIndex n) ℝ :=
    1 - R⁻¹ • ((∑ i : Fin n, MvPowerSeries.X (Sum.inr i)) +
      rho⁻¹ • MvPowerSeries.X (Sum.inl ()) + (∑ _j : Fin m, u))
  let B : MvPowerSeries (CollarCKFullIndex n) ℝ :=
    1 - R⁻¹ • (∑ i : Fin n, ∑ _j : Fin m, MvPowerSeries.pderiv (Sum.inr i) u)
  have hA : MvPowerSeries.constantCoeff A = 1 := by simp [A, h0]
  have hpartial (i : Fin n) :
      MvPowerSeries.constantCoeff (MvPowerSeries.pderiv (Sum.inr i) u) = 0 := by
    rw [← MvPowerSeries.coeff_zero_eq_constantCoeff_apply, MvPowerSeries.coeff_pderiv]
    simp [h1]
  have hB : MvPowerSeries.constantCoeff B = 1 := by simp [B, hpartial]
  have hrewrite : M • (A⁻¹ * B⁻¹ - 1) =
      MvPowerSeries.C M * (A * B)⁻¹ - MvPowerSeries.C M := by
    rw [MvPowerSeries.smul_eq_C_mul, MvPowerSeries.mul_inv_rev]
    ring
  rw [collarCKGoursatRHS_subst M R rho u h0 h1]
  change _ = M • (A⁻¹ * B⁻¹ - 1) ↔ _
  rw [hrewrite, eq_sub_iff_add_eq,
    MvPowerSeries.eq_mul_inv_iff_mul_eq (by simp [hA, hB])]
  simp only [A, B, mul_assoc]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.collarCKGoursatRHS
#print axioms GlobalEmbedding.Paper.collarCKGoursatSlots
#print axioms GlobalEmbedding.Paper.collarCKGoursatSlots_constantCoeff
#print axioms GlobalEmbedding.Paper.collarCKGoursatSlots_hasSubst
#print axioms GlobalEmbedding.Paper.collarCKGoursatRHS_subst
#print axioms GlobalEmbedding.Paper.collarCKGoursatRHS_equation_iff
