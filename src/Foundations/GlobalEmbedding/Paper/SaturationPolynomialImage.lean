import GlobalEmbedding.Paper.SaturationOpenPolynomial
import Mathlib.LinearAlgebra.Matrix.Adjugate

/-!
# Propagating actual polynomial column-image conditions

Source: `literature/parallelizable-stable-plus-one/main.tex`, prop:saturation971–985.
The Gram-adjugate numerator is a literal polynomial certificate. Local image membership
makes it zero without requiring invertibility on the local set. Its global identity
then gives an explicit preimage at every actual nonzero-Gram-determinant point.
-/

namespace GlobalEmbedding.Paper

/-- The actual Gram-adjugate numerator cancels on the actual column image.
This is just native adjugate multiplication, with no inverse hypothesis.
Source: prop:saturation, clearing the finite Gram coefficients. -/
theorem saturation_gram_adjugate_of_mem_range
    {R I J : Type*} [CommRing R] [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J R) (b : I → R) (hb : ∃ v, A.mulVec v = b) :
    A.mulVec ((A.transpose * A).adjugate.mulVec (A.transpose.mulVec b)) =
      (A.transpose * A).det • b := by
  obtain ⟨v, rfl⟩ := hb
  rw [Matrix.mulVec_mulVec v A.transpose A,
    Matrix.mulVec_mulVec v (A.transpose * A).adjugate (A.transpose * A),
    Matrix.adjugate_mul, Matrix.smul_mulVec, Matrix.one_mulVec, Matrix.mulVec_smul]

/-- An actual polynomial column-image relation on a nonempty open set holds at
EVERY point where the actual Gram determinant is nonzero. No desired global image
condition or analytic assumption is supplied. Zero row/column dimensions are allowed.
Source: prop:saturation, cone-to-global polynomial propagation. -/
theorem saturation_polynomial_image_of_open
    {σ I J : Type*} [Finite σ] [Fintype I] [Fintype J] [DecidableEq J]
    (A : Matrix I J (MvPolynomial σ ℝ)) (b : I → MvPolynomial σ ℝ)
    (U : Set (σ → ℝ)) (hU : IsOpen U) (hne : U.Nonempty)
    (h : ∀ x ∈ U, ∃ v : J → ℝ,
      (A.map (MvPolynomial.eval x)).mulVec v = fun i ↦ MvPolynomial.eval x (b i)) :
    ∀ x : σ → ℝ, MvPolynomial.eval x (A.transpose * A).det ≠ 0 →
      ∃ v : J → ℝ,
        (A.map (MvPolynomial.eval x)).mulVec v = fun i ↦ MvPolynomial.eval x (b i) := by
  let G := A.transpose * A
  have hpoly : A.mulVec (G.adjugate.mulVec (A.transpose.mulVec b)) = G.det • b := by
    apply saturation_polynomial_family_eq_of_open _ _ U hU hne
    intro x hx
    have he := saturation_gram_adjugate_of_mem_range
      (A.map (MvPolynomial.eval x)) (fun i ↦ MvPolynomial.eval x (b i)) (h x hx)
    have hg : (MvPolynomial.eval x).mapMatrix G =
        (A.map (MvPolynomial.eval x)).transpose * A.map (MvPolynomial.eval x) := by
      change (A.transpose * A).map (MvPolynomial.eval x) = _
      rw [Matrix.map_mul]
      rfl
    have ha : G.adjugate.map (MvPolynomial.eval x) =
        ((A.map (MvPolynomial.eval x)).transpose * A.map (MvPolynomial.eval x)).adjugate := by
      change (MvPolynomial.eval x).mapMatrix G.adjugate = _
      rw [RingHom.map_adjugate, hg]
    have ht : A.transpose.map (MvPolynomial.eval x) =
        (A.map (MvPolynomial.eval x)).transpose := rfl
    funext i
    simpa only [RingHom.map_mulVec, ha, Pi.smul_apply, smul_eq_mul,
      map_mul, RingHom.map_det, hg, ht, Function.comp_def] using congrFun he i
  intro x hx
  let e := MvPolynomial.eval x
  let v := (G.adjugate.map e).mulVec (fun i ↦ e ((A.transpose.mulVec b) i))
  have he : (A.map e).mulVec v = e G.det • (fun i ↦ e (b i)) := by
    funext i
    have hi := congrArg (fun w : I → MvPolynomial σ ℝ ↦ e (w i)) hpoly
    simpa only [v, RingHom.map_mulVec, Pi.smul_apply, smul_eq_mul,
      map_mul, Function.comp_def] using hi
  refine ⟨(e G.det)⁻¹ • v, ?_⟩
  rw [Matrix.mulVec_smul, he, smul_smul, inv_mul_cancel₀ hx, one_smul]

end GlobalEmbedding.Paper

#print axioms GlobalEmbedding.Paper.saturation_gram_adjugate_of_mem_range
#print axioms GlobalEmbedding.Paper.saturation_polynomial_image_of_open
