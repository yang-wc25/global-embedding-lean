import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Tactic.Module

/-!
# The actual first jet of the literal complex single-mode displacement

Source: `main.tex`, lem:increments617–620. W2.
The real displacement below is the actual coordinatewise real part of exp(i eta)(P+iQ).
No formal derivative relation, new carrier, or changed target norm is introduced.
-/

noncomputable section
namespace GlobalEmbedding.Paper

private theorem divided_phase_hasFDerivAt {n : ℕ}
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (x : EuclideanSpace ℝ (Fin n)) (hψ : DifferentiableAt ℝ ψ x) :
    HasFDerivAt (fun y ↦ ψ y / τ) (τ⁻¹ • fderiv ℝ ψ x) x := by
  have hh := hψ.hasFDerivAt.const_smul τ⁻¹
  change HasFDerivAt (fun y ↦ τ⁻¹ * ψ y) (τ⁻¹ • fderiv ℝ ψ x) x at hh
  simpa only [div_eq_mul_inv, mul_comm] using hh

/-- Differentiate the literal real part of exp(i eta)(P+iQ) on the original
finite Euclidean target. Native complex re/im identities give cos eta P−sin eta Q;
native trigonometric and scalar-product differentiation gives its actual first jet.
Source: actual phase conjugation before(6.2). -/
theorem increments_oscillatory_first_jet {n N : ℕ}
    (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (hη : DifferentiableAt ℝ η x)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)) x v =
      Real.cos (η x) • fderiv ℝ P x v - Real.sin (η x) • fderiv ℝ Q x v -
      (fderiv ℝ η x v) • (Real.sin (η x) • P x + Real.cos (η x) • Q x) := by
  have heq : (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)) =
      fun y ↦ Real.cos (η y) • P y - Real.sin (η y) • Q y := by
    funext y
    ext k
    simp [Complex.mul_re, Complex.mul_im]
  rw [heq]
  have hd := ((hη.hasFDerivAt.cos.smul hP.hasFDerivAt).sub
    (hη.hasFDerivAt.sin.smul hQ.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y ↦ Real.cos (η y) • P y - Real.sin (η y) • Q y) x = _ at hd
  rw [hd]
  simp only [add_apply, sub_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  module

/-- The actual imaginary part of the SAME literal complex mode has the
complementary phase first jet. Native real/imag multiplication identifies the
same expression with sin eta P+cos eta Q; the genuine derivative gives the
positive cosine and negative sine phase contributions. Source: conjugation(6.2). -/
theorem increments_oscillatory_im_first_jet {n N : ℕ}
    (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (hη : DifferentiableAt ℝ η x)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)) x v =
      Real.sin (η x) • fderiv ℝ P x v + Real.cos (η x) • fderiv ℝ Q x v +
      (fderiv ℝ η x v) • (Real.cos (η x) • P x - Real.sin (η x) • Q x) := by
  have heq : (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)) =
      fun y ↦ Real.sin (η y) • P y + Real.cos (η y) • Q y := by
    funext y
    ext k
    simp [Complex.mul_re, Complex.mul_im]
    ring
  rw [heq]
  have hd := ((hη.hasFDerivAt.sin.smul hP.hasFDerivAt).add
    (hη.hasFDerivAt.cos.smul hQ.hasFDerivAt)).fderiv
  change fderiv ℝ (fun y ↦ Real.sin (η y) • P y + Real.cos (η y) • Q y) x = _ at hd
  rw [hd]
  simp only [add_apply, smul_apply, ContinuousLinearMap.smulRight_apply]
  module

/-- The SAME literal mode with eta=psi/tau has the original dpsi/tau factor.
The scalar phase derivative is computed from actual differentiability, not assumed
as a phase-jet relation. The later original mode solver retains tau>0; this native
totalized identity is also valid at tau=0. Source: conjugation in617–620. -/
theorem increments_scaled_oscillatory_first_jet {n N : ℕ}
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (hψ : DifferentiableAt ℝ ψ x)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp (((ψ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)) x v =
      Real.cos (ψ x / τ) • fderiv ℝ P x v - Real.sin (ψ x / τ) • fderiv ℝ Q x v -
      (fderiv ℝ ψ x v / τ) •
        (Real.sin (ψ x / τ) • P x + Real.cos (ψ x / τ) • Q x) := by
  have hs := divided_phase_hasFDerivAt ψ τ x hψ
  have h := increments_oscillatory_first_jet (fun y ↦ ψ y / τ) P Q x v
    hs.differentiableAt hP hQ
  rw [hs.fderiv] at h
  simpa only [smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

/-- The imaginary part of the SAME psi/tau mode has its actual scaled first jet.
The phase derivative is computed once from the original psi, so both real and
imaginary components retain precisely dpsi/tau. Source: actual mode(6.2). -/
theorem increments_scaled_oscillatory_im_first_jet {n N : ℕ}
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ)
    (P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v : EuclideanSpace ℝ (Fin n)) (hψ : DifferentiableAt ℝ ψ x)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x) :
    fderiv ℝ (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp (((ψ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)) x v =
      Real.sin (ψ x / τ) • fderiv ℝ P x v + Real.cos (ψ x / τ) • fderiv ℝ Q x v +
      (fderiv ℝ ψ x v / τ) •
        (Real.cos (ψ x / τ) • P x - Real.sin (ψ x / τ) • Q x) := by
  have hs := divided_phase_hasFDerivAt ψ τ x hψ
  have h := increments_oscillatory_im_first_jet (fun y ↦ ψ y / τ) P Q x v
    hs.differentiableAt hP hQ
  rw [hs.fderiv] at h
  simpa only [smul_apply, smul_eq_mul, div_eq_mul_inv, mul_comm] using h

end GlobalEmbedding.Paper
