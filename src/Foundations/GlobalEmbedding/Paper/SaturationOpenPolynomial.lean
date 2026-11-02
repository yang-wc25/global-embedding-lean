import Mathlib.Algebra.MvPolynomial.Funext
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Order.Interval.Set.Infinite

/-!
# Real polynomial identities from nonempty open coordinate sets

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:saturation,
lines972–988. The source's open-cone identities are genuine polynomial identities.
Use Mathlib's infinite-box extensionality after extracting a box from the open set;
no polynomial-root or variable induction is reproved. Empty coordinate types remain valid.
-/

namespace GlobalEmbedding.Paper

/-- Two actual real multivariate polynomials agreeing on a nonempty open set are equal.
The box is derived from openness, rather than supplied as an additional hypothesis.
Source: prop:saturation, polynomial identity on one open cone. -/
theorem saturation_polynomial_eq_of_eqOn_open
    {σ : Type*} [Finite σ] (p q : MvPolynomial σ ℝ)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, MvPolynomial.eval x p = MvPolynomial.eval x q) : p = q := by
  obtain ⟨x, hx⟩ := hne
  obtain ⟨s, hs, hsub⟩ := isOpen_pi_iff'.1 hU x hx
  have hinf : ∀ i, (s i).Infinite := by
    intro i
    obtain ⟨a, b, hab, hbox⟩ := (hs i).1.exists_Ioo_subset ⟨x i, (hs i).2⟩
    exact (Set.Ioo_infinite hab).mono hbox
  exact MvPolynomial.funext_set s hinf (fun y hy ↦ h y (hsub hy))

/-- Vanishing on one genuine nonempty open set makes the actual polynomial zero.
Source: prop:saturation, wedge and higher-minor polynomial identities. -/
theorem saturation_polynomial_zero_of_open
    {σ : Type*} [Finite σ] (p : MvPolynomial σ ℝ)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, MvPolynomial.eval x p = 0) : p = 0 := by
  exact saturation_polynomial_eq_of_eqOn_open p 0 U hU hne (by simpa using h)

/-- Coordinatewise polynomial identities propagate simultaneously, with no nonempty
output-coordinate assumption. This applies to the actual wedge/minor coordinates.
Source: prop:saturation, the vector-valued polynomial identity step. -/
theorem saturation_polynomial_family_eq_of_open
    {σ κ : Type*} [Finite σ] (p q : κ → MvPolynomial σ ℝ)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, (fun i ↦ MvPolynomial.eval x (p i)) =
      (fun i ↦ MvPolynomial.eval x (q i))) : p = q := by
  funext i
  exact saturation_polynomial_eq_of_eqOn_open (p i) (q i) U hU hne
    (fun x hx ↦ congrFun (h x hx) i)

/-- A nonzero actual polynomial is nonzero somewhere in every nonempty open set.
No analytic premise or connectedness of that set is required.
Source: prop:saturation, choosing a good point with nonzero quadratic value. -/
theorem saturation_polynomial_exists_ne_zero_on_open
    {σ : Type*} [Finite σ] (p : MvPolynomial σ ℝ) (hp : p ≠ 0)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty) :
    ∃ x ∈ U, MvPolynomial.eval x p ≠ 0 := by
  by_contra! h
  exact hp (saturation_polynomial_zero_of_open p U hU hne h)

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_polynomial_eq_of_eqOn_open
#print axioms GlobalEmbedding.Paper.saturation_polynomial_zero_of_open
#print axioms GlobalEmbedding.Paper.saturation_polynomial_family_eq_of_open
#print axioms GlobalEmbedding.Paper.saturation_polynomial_exists_ne_zero_on_open
