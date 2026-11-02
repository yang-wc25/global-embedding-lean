import NormalPolar.InverseSqrtQuantitative
import Mathlib.Analysis.InnerProductSpace.Spectrum

/-!
# A coercive Sylvester estimate in the native operator norm

The derivative of a positive square root is self-adjoint. On that space,
H >= I implies 2 ||X|| <= ||HX + XH||. The proof uses the real spectral
basis of X only to test its eigenvalues; H need not commute with X. This
provides an explicit response constant for the actual inverse square root.
-/

noncomputable section
open scoped BigOperators

namespace GlobalEmbedding.NormalPolar

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V]
  [FiniteDimensional ℝ V]

/-- A bound for every eigenvalue of a self-adjoint operator controls its
native operator norm. The proof includes an empty spectral basis. -/
theorem selfAdjoint_norm_le_of_eigenvalue_bounds
    (X : V →L[ℝ] V) (hX : IsSelfAdjoint X) (C : ℝ) (hC : 0 ≤ C)
    (hbound : ∀ i : Fin (Module.finrank ℝ V),
      |hX.isSymmetric.eigenvalues rfl i| ≤ C) :
    ‖X‖ ≤ C := by
  let b := hX.isSymmetric.eigenvectorBasis rfl
  let a := hX.isSymmetric.eigenvalues rfl
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  have hcoord (i : Fin (Module.finrank ℝ V)) : b.repr (X v) i = a i * b.repr v i :=
    hX.isSymmetric.eigenvectorBasis_apply_self_apply rfl v i
  have hsum : ‖X v‖ ^ 2 ≤ C ^ 2 * ‖v‖ ^ 2 := by
    rw [← b.repr.norm_map (X v), ← b.repr.norm_map v,
      EuclideanSpace.real_norm_sq_eq, EuclideanSpace.real_norm_sq_eq, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    rw [hcoord, mul_pow]
    have ha : (a i) ^ 2 ≤ C ^ 2 := by
      have hh := (sq_le_sq₀ (abs_nonneg (a i)) hC).mpr (hbound i)
      simpa only [sq_abs] using hh
    exact mul_le_mul_of_nonneg_right ha (sq_nonneg _)
  have hCv : 0 ≤ C * ‖v‖ := mul_nonneg hC (norm_nonneg v)
  apply (sq_le_sq₀ (norm_nonneg _) hCv).mp
  simpa only [mul_pow] using hsum

/-- Testing HX + XH on a unit eigenvector of X yields a sharp scalar
bound, even when H and X do not commute. -/
theorem sylvester_eigenvalue_bound
    (H X : V →L[ℝ] V) (hX : IsSelfAdjoint X)
    (hH : ∀ v : V, ‖v‖ ^ 2 ≤ inner ℝ v (H v))
    (i : Fin (Module.finrank ℝ V)) :
    |hX.isSymmetric.eigenvalues rfl i| ≤ ‖H * X + X * H‖ / 2 := by
  let b := hX.isSymmetric.eigenvectorBasis rfl
  let a := hX.isSymmetric.eigenvalues rfl i
  let v := b i
  have hv : ‖v‖ = 1 := b.norm_eq_one i
  have heig : X v = a • v := hX.isSymmetric.apply_eigenvectorBasis rfl i
  have hcoer : 1 ≤ inner ℝ v (H v) := by simpa only [hv, one_pow] using hH v
  have hsymmetric : inner ℝ v (X (H v)) = inner ℝ (X v) (H v) :=
    (hX.isSymmetric v (H v)).symm
  have hinner : inner ℝ v ((H * X + X * H) v) = 2 * a * inner ℝ v (H v) := by
    change inner ℝ v (H (X v) + X (H v)) = _
    rw [inner_add_right, heig, map_smul, real_inner_smul_right,
      hsymmetric, heig, real_inner_smul_left]
    ring
  have hnorm : |inner ℝ v ((H * X + X * H) v)| ≤ ‖H * X + X * H‖ := by
    calc
      _ ≤ ‖v‖ * ‖(H * X + X * H) v‖ := abs_real_inner_le_norm _ _
      _ ≤ ‖v‖ * (‖H * X + X * H‖ * ‖v‖) :=
        mul_le_mul_of_nonneg_left ((H * X + X * H).le_opNorm v) (norm_nonneg v)
      _ = _ := by rw [hv]; ring
  rw [hinner, abs_mul, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2),
    abs_of_nonneg (by linarith : 0 ≤ inner ℝ v (H v))] at hnorm
  have ha : 0 ≤ |a| := abs_nonneg a
  nlinarith

/-- The actual operator-norm Sylvester coercivity on self-adjoint
directions. No commutation or matrix-coordinate response is assumed. -/
theorem norm_selfAdjoint_le_half_sylvester
    (H X : V →L[ℝ] V) (hX : IsSelfAdjoint X)
    (hH : ∀ v : V, ‖v‖ ^ 2 ≤ inner ℝ v (H v)) :
    ‖X‖ ≤ ‖H * X + X * H‖ / 2 := by
  exact selfAdjoint_norm_le_of_eigenvalue_bounds X hX _
    (div_nonneg (norm_nonneg _) (by norm_num))
    (sylvester_eigenvalue_bound H X hX hH)

/-- Specialize the sharp estimate to the same positive inverse square
root already constructed from the true normal compression. -/
theorem norm_selfAdjoint_le_half_actualNormalInverseSqrt_sylvester
    (K L : Submodule ℝ V) (hclose : ‖K.starProjection - L.starProjection‖ < 1)
    (X : K →L[ℝ] K) (hX : IsSelfAdjoint X) :
    ‖X‖ ≤ ‖actualNormalInverseSqrt K L * X + X * actualNormalInverseSqrt K L‖ / 2 :=
  norm_selfAdjoint_le_half_sylvester (actualNormalInverseSqrt K L) X hX
    (actualNormalInverseSqrt_coercive K L hclose)

end GlobalEmbedding.NormalPolar
