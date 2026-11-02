import GlobalEmbedding.Paper.MatrixAngleAnsatz

/-!
# The literal scalar quadratic-moment ansatz

Source: `main.tex`, `prop:matrix`, lines355–366.
DAG: `matrix-scalar-ansatz-data`.
The actual coefficient space is the Euclidean l² orthogonal sum R⊕R^m,
indexed by Option (Fin m), and all averages are actual period integrals.
-/

noncomputable section
open scoped Manifold ContDiff RealInnerProductSpace

namespace GlobalEmbedding.Paper

/-- The actual Euclidean scalar-plus-moment coefficient space.
The scalar coordinate is `none`, and the V coordinates are `some i`.
Source: `prop:matrix`, equation(3.6). -/
abbrev MatrixScalarCoefficients (m : ℕ) := EuclideanSpace ℝ (Option (Fin m))

variable {C m : ℕ}

/-- The literal integrands (η,Aη²) of the two scalar moment constraints.
Source: `prop:matrix`, lines355–360. -/
def matrixScalarMomentValues (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (q : ℝ) (z : PlanarHopfSphere C) : MatrixScalarCoefficients m :=
  WithLp.toLp 2 (fun i ↦ match i with
    | none => q
    | some j => q ^ 2 * A z j)

/-- The actual derivative (1,2Aη) of the scalar moment integrands.
Source: `prop:matrix`, line358. -/
def matrixScalarMomentDirection (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (q : ℝ) (z : PlanarHopfSphere C) : MatrixScalarCoefficients m :=
  WithLp.toLp 2 (fun i ↦ match i with
    | none => 1
    | some j => 2 * q * A z j)

/-- The literal scalar trial η_L=η_b+r cos(Lt), with r=√(2ρ) in the final
construction. Here f and the amplitudes stay fixed while L varies.
Source: `prop:matrix`, line356. -/
def matrixScalarOscillatoryBase (f : PlanarHopfSphere C → Planar)
    (ηb r : PlanarHopfSphere C → ℝ) (L : ℝ) (z : PlanarHopfSphere C) : ℝ :=
  ηb z + r z * Real.cos (L * orbitDeriv planarHopfFlow f z 1)

/-- The genuine cutoff-weighted fixed-coefficient scalar correction.
The coefficient is held fixed along the orbit when taking its moment map.
Source: `prop:matrix`, lines358–365. -/
def matrixScalarAnsatz (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (a : MatrixScalarCoefficients m)
    (z : PlanarHopfSphere C) : ℝ :=
  u z + matrixAngleCutoff κ z * ⟪matrixScalarMomentDirection A (u z) z, a⟫

/-- The actual coefficient-dependent scalar moments, not a prescribed solver.
Source: `prop:matrix`, lines358–365. -/
def matrixScalarMomentMap (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C)
    (a : MatrixScalarCoefficients m) : MatrixScalarCoefficients m :=
  orbitAverage planarHopfFlow (fun w ↦ matrixScalarMomentValues A
    (matrixScalarAnsatz A κ u a w) w) z

/-- The actual cutoff-weighted rank-one derivative Gram operator.
Source: `prop:matrix`, equation(3.6). -/
def matrixScalarGram (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    MatrixScalarCoefficients m →L[ℝ] MatrixScalarCoefficients m :=
  orbitAverage planarHopfFlow (fun w ↦ matrixAngleCutoff κ w •
    (ContinuousLinearMap.toSpanSingleton ℝ (matrixScalarMomentDirection A (u w) w)).comp
      (InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
        (matrixScalarMomentDirection A (u w) w))) z

/-- Differentiate the actual scalar quadratic integrands coordinatewise, then
transport through the genuine Euclidean l² continuous-linear equivalence.
Source: `prop:matrix`, line358. -/
theorem matrixScalarMomentValues_hasDerivAt
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (z : PlanarHopfSphere C) (q : ℝ) :
    HasDerivAt (fun x : ℝ ↦ matrixScalarMomentValues A x z)
      (matrixScalarMomentDirection A q z) q := by
  have h : HasDerivAt
      (fun x : ℝ ↦ fun i : Option (Fin m) ↦ match i with
        | none => x
        | some j => x ^ 2 * A z j)
      (fun i : Option (Fin m) ↦ match i with
        | none => 1
        | some j => 2 * q * A z j) q := by
    apply hasDerivAt_pi.mpr
    intro i
    cases i with
    | none => exact hasDerivAt_id q
    | some j => simpa using ((hasDerivAt_id q).pow 2).mul_const (A z j)
  exact (EuclideanSpace.equiv (Option (Fin m)) ℝ).symm.toContinuousLinearMap.hasFDerivAt
    |>.comp_hasDerivAt q h

/-- The scalar correction is genuinely affine in its actual coefficient vector.
Its exact derivative is the literal cutoff-weighted dual of (1,2Aη).
Source: `prop:matrix`, lines358–360. -/
theorem matrixScalarAnsatz_hasFDerivAt
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C)
    (a : MatrixScalarCoefficients m) :
    HasFDerivAt (fun c ↦ matrixScalarAnsatz A κ u c z)
      (matrixAngleCutoff κ z • InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
        (matrixScalarMomentDirection A (u z) z)) a := by
  exact ((InnerProductSpace.toDual ℝ (MatrixScalarCoefficients m)
    (matrixScalarMomentDirection A (u z) z)).hasFDerivAt.const_mul
      (matrixAngleCutoff κ z)).const_add (u z)

/-- At coefficient zero the scalar ansatz is exactly its original trial function.
Source: `prop:matrix`, lines356–358. -/
@[simp] theorem matrixScalarAnsatz_zero
    (A : PlanarHopfSphere C → EuclideanSpace ℝ (Fin m))
    (κ u : PlanarHopfSphere C → ℝ) (z : PlanarHopfSphere C) :
    matrixScalarAnsatz A κ u 0 z = u z := by
  simp [matrixScalarAnsatz]

#print axioms matrixScalarMomentValues_hasDerivAt
#print axioms matrixScalarAnsatz_hasFDerivAt
#print axioms matrixScalarAnsatz_zero

end GlobalEmbedding.Paper
