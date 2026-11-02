import Initialization.Colored.SmoothMap
import Mathlib.Analysis.Calculus.FDeriv.Mul
import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-!
# The actual first derivative and common-rate error of (7.2)

The exact derivative of a literal cutoff times complex exponential separates
into the differentiated-cutoff term and the phase-rate discrepancy. No formal
jet is substituted for the derivative of the constructed function.
-/

noncomputable section

open Function Set Metric Manifold
open scoped ContDiff Topology

namespace GlobalEmbedding.Initialization

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The actual complex linear phase insertion, with the original factor 2π. -/
def coloredPhaseLinear (T : ℝ) : ℝ →L[ℝ] ℂ :=
  (((2 * Real.pi * T : ℝ) : ℂ) * Complex.I) • Complex.ofRealCLM

/-- The derivative of one actual term of (7.2). -/
def coloredWaveDerivative (χ ℓ : E → ℝ) (dχ dℓ : E →L[ℝ] ℝ)
    (T : ℝ) (x : E) : E →L[ℝ] ℂ :=
  χ x • ((Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) •
    ((coloredPhaseLinear T).comp dℓ)) +
      dχ.smulRight (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ)

/-- Direct application of the exponential and product differentiation rules
proves that the declared expression is the derivative of the literal map. -/
theorem coloredWave_hasFDerivAt (χ ℓ : E → ℝ) (dχ dℓ : E →L[ℝ] ℝ)
    (T : ℝ) (x : E) (hχ : HasFDerivAt χ dχ x) (hℓ : HasFDerivAt ℓ dℓ x) :
    HasFDerivAt (coloredWave χ ℓ T) (coloredWaveDerivative χ ℓ dχ dℓ T x) x := by
  have he := ((coloredPhaseLinear T).hasFDerivAt.comp x hℓ).cexp
  have hid (y : E) : Complex.exp (coloredPhaseLinear T (ℓ y)) =
      (Circle.exp (2 * Real.pi * T * ℓ y) : ℂ) := by
    congr 1
    simp only [coloredPhaseLinear, smul_apply,
      Complex.ofRealCLM_apply, smul_eq_mul, Complex.ofReal_mul]
    ring
  have he' : HasFDerivAt (fun y ↦ (Circle.exp (2 * Real.pi * T * ℓ y) : ℂ))
      ((Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) • ((coloredPhaseLinear T).comp dℓ)) x := by
    simpa only [Function.comp_apply, hid] using he
  exact hχ.smul he'

/-- The computed expression equals Lean's actual total Fréchet derivative. -/
theorem coloredWave_fderiv (χ ℓ : E → ℝ) (dχ dℓ : E →L[ℝ] ℝ)
    (T : ℝ) (x : E) (hχ : HasFDerivAt χ dχ x) (hℓ : HasFDerivAt ℓ dℓ x) :
    fderiv ℝ (coloredWave χ ℓ T) x = coloredWaveDerivative χ ℓ dχ dℓ T x :=
  (coloredWave_hasFDerivAt χ ℓ dχ dℓ T x hχ hℓ).fderiv

/-- Replacing every local phase rate by one common real covector leaves exactly
these two errors: a differentiated cutoff and the actual phase-rate difference.
The common covector is in rescaled coordinates and already includes T. -/
theorem coloredWave_first_error_identity (χ ℓ : E → ℝ) (dχ dℓ r : E →L[ℝ] ℝ)
    (T : ℝ) (x v : E) (hχ : HasFDerivAt χ dχ x) (hℓ : HasFDerivAt ℓ dℓ x) :
    fderiv ℝ (coloredWave χ ℓ T) x v -
      χ x • (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) * (r v : ℂ)) =
      dχ v • (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) +
      χ x • (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) * ((T * dℓ v - r v : ℝ) : ℂ)) := by
  rw [coloredWave_fderiv χ ℓ dχ dℓ T x hχ hℓ]
  simp only [coloredWaveDerivative, coloredPhaseLinear,
    add_apply, smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.smulRight_apply,
    Complex.ofRealCLM_apply, Complex.ofReal_mul, Complex.ofReal_sub,
    RCLike.real_smul_eq_coe_mul, smul_eq_mul]
  ring

/-- The same exact derivative has the pointwise quantitative error that drives
K⁻¹+K/T after inserting the actual geometric rate and cutoff estimates. -/
theorem coloredWave_first_error_bound (χ ℓ : E → ℝ) (dχ dℓ r : E →L[ℝ] ℝ)
    (T : ℝ) (x v : E) (hχ : HasFDerivAt χ dχ x) (hℓ : HasFDerivAt ℓ dℓ x) :
    ‖fderiv ℝ (coloredWave χ ℓ T) x v -
      χ x • (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) * (r v : ℂ))‖ ≤
      |dχ v| + |χ x| * (2 * Real.pi) * |T * dℓ v - r v| := by
  rw [coloredWave_first_error_identity χ ℓ dχ dℓ r T x v hχ hℓ]
  calc
    _ ≤ ‖dχ v • (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ)‖ +
      ‖χ x • (((2 * Real.pi : ℝ) : ℂ) * Complex.I *
        (Circle.exp (2 * Real.pi * T * ℓ x) : ℂ) * ((T * dℓ v - r v : ℝ) : ℂ))‖ :=
      norm_add_le _ _
    _ = |dχ v| + |χ x| * (2 * Real.pi) * |T * dℓ v - r v| := by
      simp only [norm_smul, norm_mul, Circle.norm_coe, Complex.norm_I,
        Complex.norm_real, Real.norm_eq_abs, abs_of_pos Real.pi_pos,
        mul_one]
      ring

end GlobalEmbedding.Initialization
