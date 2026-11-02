import GlobalEmbedding.Paper.PlanarHopfCurvature
import Mathlib.Analysis.InnerProductSpace.Dual
import Mathlib.Analysis.SpecialFunctions.SmoothTransition
import Mathlib.Data.Fin.VecNotation
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Deriv

/-!
# The literal four-moment angle ansatz

Source: `main.tex`, `prop:matrix`, lines299–323. The coefficient space has its actual
Euclidean l² norm. Every derivative, average and cutoff below is the native actual object.
-/

noncomputable section

open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- The four actual correction coefficients, with Euclidean norm. -/
abbrev MatrixAngleCoefficients := EuclideanSpace ℝ (Fin 4)

variable {C : ℕ}

/-- The actual scalar b=inner(f,J₂Xf) in the original four moments. -/
def matrixAngleNormalPosition (f : PlanarHopfSphere C → Planar) (z : PlanarHopfSphere C) : ℝ :=
  ⟪f z, planarQuarterTurn (orbitDeriv planarHopfFlow f z)⟫

/-- The original four moment integrands at a literal scalar angle. -/
def matrixAngleMomentValues (f : PlanarHopfSphere C → Planar)
    (θ : ℝ) (z : PlanarHopfSphere C) : MatrixAngleCoefficients :=
  WithLp.toLp 2 ![Real.cos θ, orbitDeriv planarHopfFlow f z 1 * Real.sin θ,
    orbitDeriv planarHopfFlow f z 0 * Real.cos θ, matrixAngleNormalPosition f z * Real.sin θ]

/-- The literal derivative of the four moment integrands with respect to their angle. -/
def matrixAngleMomentDirection (f : PlanarHopfSphere C → Planar)
    (θ : ℝ) (z : PlanarHopfSphere C) : MatrixAngleCoefficients :=
  WithLp.toLp 2 ![-Real.sin θ, orbitDeriv planarHopfFlow f z 1 * Real.cos θ,
    -(orbitDeriv planarHopfFlow f z 0) * Real.sin θ,
    matrixAngleNormalPosition f z * Real.cos θ]

/-- The actual F_T of the original proof, not an assumed moment derivative. -/
def matrixAngleBaseProfile (f : PlanarHopfSphere C → Planar)
    (T : ℝ) (z : PlanarHopfSphere C) : MatrixAngleCoefficients :=
  matrixAngleMomentDirection f (T * orbitDeriv planarHopfFlow f z 1) z

/-- The actual flat curvature cutoff rho0. -/
def matrixAngleCutoff (κ : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) : ℝ :=
  expNegInvGlue (κ z ^ 2)

/-- The literal angle with one fixed coefficient vector, before selecting the basic roots. -/
def matrixAngleAnsatz (f : PlanarHopfSphere C → Planar) (κ : PlanarHopfSphere C → ℝ)
    (T : ℝ) (a : MatrixAngleCoefficients) (z : PlanarHopfSphere C) : ℝ :=
  T * orbitDeriv planarHopfFlow f z 1 +
    matrixAngleCutoff κ z * ⟪matrixAngleBaseProfile f T z, a⟫

/-- The actual period average of the four moments; a stays fixed throughout the orbit. -/
def matrixAngleMomentMap (f : PlanarHopfSphere C → Planar) (κ : PlanarHopfSphere C → ℝ)
    (T : ℝ) (z : PlanarHopfSphere C) (a : MatrixAngleCoefficients) : MatrixAngleCoefficients :=
  orbitAverage planarHopfFlow
    (fun w ↦ matrixAngleMomentValues f (matrixAngleAnsatz f κ T a w) w) z

/-- The actual weighted Gram operator: a maps to av(rho0 inner(F_T,a) F_T).
This is a literal continuous-linear-map-valued period integral. -/
def matrixAngleGram (f : PlanarHopfSphere C → Planar) (κ : PlanarHopfSphere C → ℝ)
    (T : ℝ) (z : PlanarHopfSphere C) : MatrixAngleCoefficients →L[ℝ] MatrixAngleCoefficients :=
  orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w •
    (ContinuousLinearMap.toSpanSingleton ℝ (matrixAngleBaseProfile f T w)).comp
      (InnerProductSpace.toDual ℝ MatrixAngleCoefficients (matrixAngleBaseProfile f T w))) z

/-- The actual angle derivative of the original four moment values. -/
theorem matrixAngleMomentValues_hasDerivAt (f : PlanarHopfSphere C → Planar)
    (z : PlanarHopfSphere C) (θ : ℝ) :
    HasDerivAt (fun q : ℝ ↦ matrixAngleMomentValues f q z)
      (matrixAngleMomentDirection f θ z) θ := by
  have h : HasDerivAt
      (fun q : ℝ ↦ ![Real.cos q, orbitDeriv planarHopfFlow f z 1 * Real.sin q,
        orbitDeriv planarHopfFlow f z 0 * Real.cos q,
        matrixAngleNormalPosition f z * Real.sin q])
      ![-Real.sin θ, orbitDeriv planarHopfFlow f z 1 * Real.cos θ,
        -(orbitDeriv planarHopfFlow f z 0) * Real.sin θ,
        matrixAngleNormalPosition f z * Real.cos θ] θ := by
    apply hasDerivAt_pi.mpr
    intro i
    fin_cases i
    · simpa using Real.hasDerivAt_cos θ
    · simpa using (Real.hasDerivAt_sin θ).const_mul (orbitDeriv planarHopfFlow f z 1)
    · convert (Real.hasDerivAt_cos θ).const_mul (orbitDeriv planarHopfFlow f z 0) using 1 <;> simp
    · simpa using (Real.hasDerivAt_sin θ).const_mul (matrixAngleNormalPosition f z)
  exact (EuclideanSpace.equiv (Fin 4) ℝ).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt θ h

/-- At coefficient zero the angle is exactly the original high-frequency phase. -/
@[simp] theorem matrixAngleAnsatz_zero (f : PlanarHopfSphere C → Planar)
    (κ : PlanarHopfSphere C → ℝ) (T : ℝ) (z : PlanarHopfSphere C) :
    matrixAngleAnsatz f κ T 0 z = T * orbitDeriv planarHopfFlow f z 1 := by
  simp [matrixAngleAnsatz]

end GlobalEmbedding.Paper
