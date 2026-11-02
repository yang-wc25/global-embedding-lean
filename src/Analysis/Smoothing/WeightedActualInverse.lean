import GlobalEmbedding.Paper.InverseDerivativeBounds
import Mathlib.Analysis.Calculus.ContDiff.Operations

/-!
# Uniform slow derivatives of the actual inverse field

Source: main.tex (6.2), (6.4)--(6.5), the actual slow inverse coefficients.
The original inverse-derivative theorem is used on the genuine rescaled open
domain. The exact invertible-dilation chain rule retains ell^j. Consequently
the inverse majorant is independent of ell, the ambient dimension and the
chart count. The field inverted is exactly the supplied geometric field P.
-/

noncomputable section
open GlobalEmbedding.Paper Set Function
open scoped ContDiff BigOperators

namespace GlobalEmbedding.Continuation

section Dilation
variable {D Y : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedAddCommGroup Y] [NormedSpace ℝ Y]

/-- The actual invertible real dilation of a normed source model. -/
def slowDilation (ell : ℝ) (hell : ell ≠ 0) : D ≃L[ℝ] D where
  toLinearEquiv := LinearEquiv.smulOfNeZero ℝ D ell hell
  continuous_toFun := continuous_id.const_smul ell
  continuous_invFun := continuous_id.const_smul ell⁻¹

@[simp] theorem slowDilation_apply (ell : ℝ) (hell : ell ≠ 0) (x : D) :
    slowDilation ell hell x = ell • x := rfl

@[simp] theorem slowDilation_symm_apply (ell : ℝ) (hell : ell ≠ 0) (x : D) :
    (slowDilation ell hell).symm x = ell⁻¹ • x := rfl

/-- Exact all-order chain rule for the same field on a rescaled open domain.
Invertibility makes this equality valid even for totalized native derivatives. -/
theorem iteratedFDeriv_slowDilation (f : D → Y) (ell : ℝ) (hell : ell ≠ 0)
    (j : ℕ) (x : D) :
    iteratedFDeriv ℝ j (f ∘ slowDilation ell hell) x =
      ell ^ j • iteratedFDeriv ℝ j f (ell • x) := by
  have he := (slowDilation (D := D) ell hell).iteratedFDerivWithin_comp_right f
    uniqueDiffOn_univ (x := x) (mem_univ _) j
  simp only [preimage_univ, iteratedFDerivWithin_univ] at he
  rw [he]
  ext v
  change iteratedFDeriv ℝ j f (ell • x) (fun i => ell • v i) =
    ell ^ j • iteratedFDeriv ℝ j f (ell • x) v
  simpa only [Finset.prod_const, Finset.card_univ, Fintype.card_fin] using
    (iteratedFDeriv ℝ j f (ell • x)).map_smul_univ (fun _ => ell) v

/-- Native derivative norms carry the exact slow weight, with no lost powers. -/
theorem norm_iteratedFDeriv_slowDilation (f : D → Y) (ell : ℝ) (hell : 0 < ell)
    (j : ℕ) (x : D) :
    ‖iteratedFDeriv ℝ j (f ∘ slowDilation ell hell.ne') x‖ =
      ell ^ j * ‖iteratedFDeriv ℝ j f (ell • x)‖ := by
  rw [iteratedFDeriv_slowDilation, norm_smul, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg hell.le j)]

end Dilation

/-- An explicit finite majorant chosen before all spaces, fields and scales. -/
def slowInverseMajorant (b M : ℝ) : ℕ → ℝ
  | 0 => 1 + b
  | k+1 => slowInverseMajorant b M k + 4 ^ k * slowInverseMajorant b M k ^ 2 * M

theorem slowInverseMajorant_nonneg {b M : ℝ} (hb : 0 ≤ b) (hM : 0 ≤ M) (k : ℕ) :
    0 ≤ slowInverseMajorant b M k := by
  induction k with
  | zero => simp only [slowInverseMajorant]; positivity
  | succ k hk => simp only [slowInverseMajorant]; positivity

theorem slowInverseMajorant_mono {b M : ℝ} (hM : 0 ≤ M) : Monotone (slowInverseMajorant b M) := by
  apply monotone_nat_of_le_succ
  intro k
  simp only [slowInverseMajorant]
  exact le_add_of_nonneg_right (by positivity)

/-- The actual inverse inherits slow weighted jets on the same original open
domain. This strengthens the unweighted theorem by a genuine change of variables,
without assuming the desired inverse derivative bound or reducing the domain. -/
theorem actual_inverse_slow_weighted_jets
    {D A : Type*} [NormedAddCommGroup D] [NormedSpace ℝ D]
    [NormedRing A] [NormedAlgebra ℝ A] [CompleteSpace A]
    (j : ℕ) (O : Set D) (hO : IsOpen O) (P : D → A)
    (hP : ContDiffOn ℝ ∞ P O) (hunit : ∀ x ∈ O, IsUnit (P x))
    (ell b M : ℝ) (hell : 0 < ell) (hb : 0 ≤ b) (hM : 0 ≤ M)
    (hval : ∀ x ∈ O, ‖Ring.inverse (P x)‖ ≤ b)
    (hjet : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ O,
      ell ^ k * ‖iteratedFDeriv ℝ k P x‖ ≤ M) :
    ∀ k ≤ j, ∀ r ≤ k, ∀ x ∈ O,
      ell ^ r * ‖iteratedFDeriv ℝ r (fun y => Ring.inverse (P y)) x‖ ≤
        slowInverseMajorant b M k := by
  let e := slowDilation (D := D) ell hell.ne'
  let V := e ⁻¹' O
  let Q := P ∘ e
  have hV : IsOpen V := hO.preimage e.continuous
  have hQ : ContDiffOn ℝ ∞ Q V := hP.comp e.contDiff.contDiffOn (fun _ hy => hy)
  have hQunit : ∀ x ∈ V, IsUnit (Q x) := fun x hx => hunit (e x) hx
  have hQval : ∀ x ∈ V, ‖Ring.inverse (Q x)‖ ≤ b := fun x hx => hval (e x) hx
  have hQjet : ∀ k, 1 ≤ k → k ≤ j → ∀ x ∈ V, ‖iteratedFDeriv ℝ k Q x‖ ≤ M := by
    intro k hk hkj x hx
    rw [norm_iteratedFDeriv_slowDilation P ell hell k x]
    exact hjet k hk hkj (e x) hx
  have hi := inverse_derivative_bounds j V hV Q hQ hQunit b M hb hM hQval hQjet
    (slowInverseMajorant b M) rfl (fun _ => rfl)
  intro k hkj r hr x hx
  have hx' : e.symm x ∈ V := by
    change e (e.symm x) ∈ O
    simpa only [e.apply_symm_apply] using hx
  have h := hi k hkj r hr (e.symm x) hx'
  change ‖iteratedFDeriv ℝ r ((fun y => Ring.inverse (P y)) ∘ e) (e.symm x)‖ ≤ _ at h
  rw [norm_iteratedFDeriv_slowDilation _ ell hell r (e.symm x)] at h
  have he : ell • e.symm x = x := e.apply_symm_apply x
  rwa [he] at h

end GlobalEmbedding.Continuation

#print axioms GlobalEmbedding.Continuation.iteratedFDeriv_slowDilation
#print axioms GlobalEmbedding.Continuation.actual_inverse_slow_weighted_jets
