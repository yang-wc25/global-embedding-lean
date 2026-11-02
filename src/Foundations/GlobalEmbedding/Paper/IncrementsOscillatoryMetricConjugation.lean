import GlobalEmbedding.Paper.IncrementsCoordinateMetricVariation
import GlobalEmbedding.Paper.IncrementsOscillatoryFirstJet
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# Literal complex phase conjugation of the actual induced metric variation

Source: `main.tex`, lem:increments617–620. W2.
Every metric variation is the literal real derivative of inducedMetric(F+sZ).
The actual finite-coordinate exp/re/im calculus proves differentiability of the
phased fields. No formal phase or metric-variation identity is assumed.
-/

noncomputable section
open Manifold
open scoped ContDiff

namespace GlobalEmbedding.Paper

/-- The literal original Dgamma(F)Z, with the actual coordinate tangent casts.
This abbreviation is only the real derivative of the existing inducedMetric;
it is not a replacement formal tensor. Source: linearized metric in617–620. -/
abbrev incrementsCoordinateMetricVariation {n N : ℕ}
    (F Z : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x v w : EuclideanSpace ℝ (Fin n)) : ℝ :=
  deriv (fun s : ℝ ↦ inducedMetric (I := 𝓘(ℝ, EuclideanSpace ℝ (Fin n)))
    (fun y ↦ F y + s • Z y) x
    ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm v)
    ((tangentSpaceCastModel 𝓘(ℝ, EuclideanSpace ℝ (Fin n)) x).symm w)) 0

private theorem phased_fields_differentiableAt {n N : ℕ}
    (η : EuclideanSpace ℝ (Fin n) → ℝ)
    (P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (x : EuclideanSpace ℝ (Fin n)) (hη : DifferentiableAt ℝ η x)
    (hP : DifferentiableAt ℝ P x) (hQ : DifferentiableAt ℝ Q x) :
    DifferentiableAt ℝ (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)) x ∧
    DifferentiableAt ℝ (fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)) x := by
  have hphase := ((Complex.ofRealCLM.differentiableAt.comp x hη).mul_const Complex.I).cexp
  have hc (k : Fin N) : DifferentiableAt ℝ (fun y ↦
      Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))) x := by
    let pk : EuclideanSpace ℝ (Fin N) →L[ℝ] ℝ := EuclideanSpace.proj k
    have hp : DifferentiableAt ℝ (fun y ↦ (P y k : ℂ)) x :=
      Complex.ofRealCLM.differentiableAt.comp x (pk.differentiableAt.comp x hP)
    have hq : DifferentiableAt ℝ (fun y ↦ (Q y k : ℂ)) x :=
      Complex.ofRealCLM.differentiableAt.comp x (pk.differentiableAt.comp x hQ)
    have hh := hphase.mul (hp.add ((differentiableAt_const Complex.I).mul hq))
    change DifferentiableAt ℝ (fun y ↦ Complex.exp ((η y : ℂ) * Complex.I) *
      ((P y k : ℂ) + Complex.I * (Q y k : ℂ))) x at hh
    exact hh
  constructor
  · have hp := differentiableAt_pi.mpr fun k ↦ Complex.reCLM.differentiableAt.comp x (hc k)
    exact (EuclideanSpace.equiv (Fin N) ℝ).symm.differentiableAt.comp x hp
  · have hp := differentiableAt_pi.mpr fun k ↦ Complex.imCLM.differentiableAt.comp x (hc k)
    exact (EuclideanSpace.equiv (Fin N) ℝ).symm.differentiableAt.comp x hp

/-- Actual complex conjugation of the SAME real induced-metric variation.

The literal real/imaginary phased displacements are genuinely differentiable.
Use the accepted actual inducedMetric derivative and actual phase first jets to
compute both metric components. Native real inner bilinearity identifies their
complex sum as exp(i eta) times the plain actual variation plus its actual lowered
covector phase term. Native exp addition cancels exp(-i eta). No variation,
phase-commutation, normality or cancellation identity is an input.
Source: conjugation adding (i/tau)(delta_i1 u_j+delta_j1 u_i) in617–620. -/
theorem increments_oscillatory_metric_conjugation {n N : ℕ}
    (F P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (η : EuclideanSpace ℝ (Fin n) → ℝ) (x v w : EuclideanSpace ℝ (Fin n))
    (hF : DifferentiableAt ℝ F x) (hP : DifferentiableAt ℝ P x)
    (hQ : DifferentiableAt ℝ Q x) (hη : DifferentiableAt ℝ η x) :
    let R := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)
    let S := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp ((η y : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)
    Complex.exp (-(η x : ℂ) * Complex.I) *
      ((incrementsCoordinateMetricVariation F R x v w : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation F S x v w : ℂ)) =
      (incrementsCoordinateMetricVariation F P x v w : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation F Q x v w : ℂ) +
      Complex.I * ((fderiv ℝ η x v : ℂ) *
          ((inner ℝ (fderiv ℝ F x w) (P x) : ℂ) +
            Complex.I * (inner ℝ (fderiv ℝ F x w) (Q x) : ℂ)) +
        (fderiv ℝ η x w : ℂ) *
          ((inner ℝ (fderiv ℝ F x v) (P x) : ℂ) +
            Complex.I * (inner ℝ (fderiv ℝ F x v) (Q x) : ℂ))) := by
  let R := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
    (Complex.exp ((η y : ℂ) * Complex.I) *
      ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)
  let S := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
    (Complex.exp ((η y : ℂ) * Complex.I) *
      ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)
  have hdiff := phased_fields_differentiableAt η P Q x hη hP hQ
  have hp := (increments_inducedMetric_hasDerivAt F P x v w hF hP).deriv
  have hq := (increments_inducedMetric_hasDerivAt F Q x v w hF hQ).deriv
  have hr := (increments_inducedMetric_hasDerivAt F R x v w hF hdiff.1).deriv
  have hs := (increments_inducedMetric_hasDerivAt F S x v w hF hdiff.2).deriv
  change incrementsCoordinateMetricVariation F P x v w = _ at hp
  change incrementsCoordinateMetricVariation F Q x v w = _ at hq
  change incrementsCoordinateMetricVariation F R x v w = _ at hr
  change incrementsCoordinateMetricVariation F S x v w = _ at hs
  have hreal : incrementsCoordinateMetricVariation F R x v w =
      Real.cos (η x) * incrementsCoordinateMetricVariation F P x v w -
      Real.sin (η x) * incrementsCoordinateMetricVariation F Q x v w -
      fderiv ℝ η x v * (Real.sin (η x) * inner ℝ (fderiv ℝ F x w) (P x) +
        Real.cos (η x) * inner ℝ (fderiv ℝ F x w) (Q x)) -
      fderiv ℝ η x w * (Real.sin (η x) * inner ℝ (fderiv ℝ F x v) (P x) +
        Real.cos (η x) * inner ℝ (fderiv ℝ F x v) (Q x)) := by
    rw [hr, hp, hq]
    rw [increments_oscillatory_first_jet η P Q x v hη hP hQ,
      increments_oscillatory_first_jet η P Q x w hη hP hQ]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  have himag : incrementsCoordinateMetricVariation F S x v w =
      Real.sin (η x) * incrementsCoordinateMetricVariation F P x v w +
      Real.cos (η x) * incrementsCoordinateMetricVariation F Q x v w +
      fderiv ℝ η x v * (Real.cos (η x) * inner ℝ (fderiv ℝ F x w) (P x) -
        Real.sin (η x) * inner ℝ (fderiv ℝ F x w) (Q x)) +
      fderiv ℝ η x w * (Real.cos (η x) * inner ℝ (fderiv ℝ F x v) (P x) -
        Real.sin (η x) * inner ℝ (fderiv ℝ F x v) (Q x)) := by
    rw [hs, hp, hq]
    rw [increments_oscillatory_im_first_jet η P Q x v hη hP hQ,
      increments_oscillatory_im_first_jet η P Q x w hη hP hQ]
    simp only [inner_sub_left, inner_sub_right, inner_add_left, inner_add_right,
      real_inner_smul_left, inner_smul_right, real_inner_comm]
    ring
  have hmode : (incrementsCoordinateMetricVariation F R x v w : ℂ) +
      Complex.I * (incrementsCoordinateMetricVariation F S x v w : ℂ) =
      Complex.exp ((η x : ℂ) * Complex.I) *
        ((incrementsCoordinateMetricVariation F P x v w : ℂ) +
          Complex.I * (incrementsCoordinateMetricVariation F Q x v w : ℂ) +
          Complex.I * ((fderiv ℝ η x v : ℂ) *
            ((inner ℝ (fderiv ℝ F x w) (P x) : ℂ) +
              Complex.I * (inner ℝ (fderiv ℝ F x w) (Q x) : ℂ)) +
            (fderiv ℝ η x w : ℂ) *
            ((inner ℝ (fderiv ℝ F x v) (P x) : ℂ) +
              Complex.I * (inner ℝ (fderiv ℝ F x v) (Q x) : ℂ)))) := by
    rw [hreal, himag, Complex.exp_ofReal_mul_I]
    apply Complex.ext <;> simp [Complex.mul_re, Complex.mul_im] <;> ring
  change Complex.exp (-(η x : ℂ) * Complex.I) *
    ((incrementsCoordinateMetricVariation F R x v w : ℂ) +
      Complex.I * (incrementsCoordinateMetricVariation F S x v w : ℂ)) = _
  rw [hmode, ← mul_assoc, ← Complex.exp_add]
  simp [neg_mul]

/-- The SAME actual metric conjugation for the original phase psi/tau.
Native differentiation computes the actual dpsi/tau factors. No prescribed
phase-jet identity is an input. Source: original conjugation in617–620. -/
theorem increments_scaled_oscillatory_metric_conjugation {n N : ℕ}
    (F P Q : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin N))
    (ψ : EuclideanSpace ℝ (Fin n) → ℝ) (τ : ℝ) (x v w : EuclideanSpace ℝ (Fin n))
    (hF : DifferentiableAt ℝ F x) (hP : DifferentiableAt ℝ P x)
    (hQ : DifferentiableAt ℝ Q x) (hψ : DifferentiableAt ℝ ψ x) :
    let R := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp (((ψ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).re)
    let S := fun y ↦ WithLp.toLp 2 (fun k : Fin N ↦
      (Complex.exp (((ψ y / τ : ℝ) : ℂ) * Complex.I) *
        ((P y k : ℂ) + Complex.I * (Q y k : ℂ))).im)
    Complex.exp (-((ψ x / τ : ℝ) : ℂ) * Complex.I) *
      ((incrementsCoordinateMetricVariation F R x v w : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation F S x v w : ℂ)) =
      (incrementsCoordinateMetricVariation F P x v w : ℂ) +
        Complex.I * (incrementsCoordinateMetricVariation F Q x v w : ℂ) +
      Complex.I * ((fderiv ℝ ψ x v / τ : ℂ) *
          ((inner ℝ (fderiv ℝ F x w) (P x) : ℂ) +
            Complex.I * (inner ℝ (fderiv ℝ F x w) (Q x) : ℂ)) +
        (fderiv ℝ ψ x w / τ : ℂ) *
          ((inner ℝ (fderiv ℝ F x v) (P x) : ℂ) +
            Complex.I * (inner ℝ (fderiv ℝ F x v) (Q x) : ℂ))) := by
  have hs : HasFDerivAt (fun y ↦ ψ y / τ) (τ⁻¹ • fderiv ℝ ψ x) x := by
    have hh := hψ.hasFDerivAt.const_smul τ⁻¹
    change HasFDerivAt (fun y ↦ τ⁻¹ * ψ y) (τ⁻¹ • fderiv ℝ ψ x) x at hh
    simpa only [div_eq_mul_inv, mul_comm] using hh
  have h := increments_oscillatory_metric_conjugation F P Q (fun y ↦ ψ y / τ)
    x v w hF hP hQ hs.differentiableAt
  dsimp only at h ⊢
  rw [hs.fderiv] at h
  simpa only [smul_apply, smul_eq_mul, div_eq_mul_inv, Complex.ofReal_mul,
    Complex.ofReal_inv, mul_comm] using h

end GlobalEmbedding.Paper
