import NormalPolar.ConstructionPositiveBranch
import Mathlib.Analysis.Matrix.Order

/-!
# Uniqueness of the positive compression square root

The explicit real-operator series is independent of a different presentation
of the positive inverse square root. A finite orthonormal basis transfers only
the uniqueness proof to Mathlib's matrix functional calculus; the actual
normal identification remains the already constructed map.
-/

noncomputable section
open scoped MatrixOrder

namespace GlobalEmbedding.NormalPolar
open GlobalEmbedding.Continuation

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

private theorem positive_matrix_eq_of_mul_self_eq
    {ι : Type*} [Fintype ι] [DecidableEq ι]
    (A B : Matrix ι ι ℝ) (hA : A.PosSemidef) (hB : B.PosSemidef)
    (hsq : A * A = B * B) : A = B :=
  (CFC.mul_self_eq_mul_self_iff A B hA.nonneg hB.nonneg).mp hsq

/-- Positivity removes the ambiguity in a square root of a real Hilbert-space
endomorphism, including the zero-dimensional case. -/
theorem positive_operator_eq_of_mul_self_eq
    (A B : V →L[ℝ] V) (hA : A.IsPositive) (hB : B.IsPositive)
    (hsq : A * A = B * B) : A = B := by
  let b := stdOrthonormalBasis ℝ V
  let e := LinearMap.toMatrixAlgEquiv b.toBasis
  have hAp : (e A.toLinearMap).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).mpr hA
  have hBp : (e B.toLinearMap).PosSemidef :=
    (LinearMap.posSemidef_toMatrix_iff b).mpr hB
  have hlinear : A.toLinearMap * A.toLinearMap = B.toLinearMap * B.toLinearMap := by
    ext v
    exact congrArg (fun T : V →L[ℝ] V ↦ T v) hsq
  have hmat : e A.toLinearMap * e A.toLinearMap =
      e B.toLinearMap * e B.toLinearMap := by
    rw [← map_mul, ← map_mul, hlinear]
  have heq := positive_matrix_eq_of_mul_self_eq (e A.toLinearMap) (e B.toLinearMap)
    hAp hBp hmat
  ext v
  exact congrArg (fun T : V →ₗ[ℝ] V ↦ T v) (e.injective heq)

/-- Every genuine positive inverse-square-root presentation of the same true
normal compression agrees with the explicit series construction. -/
theorem eq_actualNormalInverseSqrt_of_positive_sq
    (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1)
    (H : K →L[ℝ] K) (hH : H.IsPositive)
    (hsq : H * H = (normalProjectionCompression K L.starProjection).inverse) :
    H = actualNormalInverseSqrt K L := by
  apply positive_operator_eq_of_mul_self_eq H (actualNormalInverseSqrt K L)
    hH (actualNormalInverseSqrt_positive K L hclose)
  rw [hsq, ← actualNormalInverseSqrt_sq_eq_inverse K L hclose]

/-- Thus a positively normalized compression formula supplies the same Qop,
with no change of normal identification hidden in its presentation. -/
theorem positive_compression_formula_eq_actualPolarOperator
    (K L : Submodule ℝ V)
    (hclose : ‖K.starProjection - L.starProjection‖ < 1)
    (H : K →L[ℝ] K) (hH : H.IsPositive)
    (hsq : H * H = (normalProjectionCompression K L.starProjection).inverse) :
    K.subtypeL.comp (H.comp (K.orthogonalProjectionOnto.comp L.starProjection)) =
      actualPolarOperator K.starProjection L.starProjection := by
  rw [eq_actualNormalInverseSqrt_of_positive_sq K L hclose H hH hsq]
  exact (actualPolarOperator_eq_compression_formula K L).symm

end GlobalEmbedding.NormalPolar
