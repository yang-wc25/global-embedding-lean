import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# Faithful Euclidean coordinates for every finite-dimensional continuous linear operator

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–418.
DAG node: `balanced-holder-hilbert-schmidt-coordinate-equiv`.
-/

open WithLp

namespace GlobalEmbedding.Paper

/-- Flat Euclidean matrix coefficients are linearly equivalent to ALL continuous linear maps
between the declared Euclidean spaces. The coordinate norm is calibrated to Hilbert–Schmidt
separately; this equivalence does not identify it with the default operator norm.

Use the explicit coefficient-index bijection to and from matrices, Mathlib's Euclidean
matrix-to-linear-map equivalence, and finite-domain continuity. The inverse is the actual
matrix of the operator in the standard orthonormal bases.
Source: Hilbert–Schmidt coefficient model for Holder multiplication in `lem:balanced`. -/
noncomputable def hilbertSchmidtCoordinateEquiv (M N : ℕ) :
    EuclideanSpace ℝ (Fin (N * M)) ≃ₗ[ℝ]
      (EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N)) := by
  let e : EuclideanSpace ℝ (Fin (N * M)) ≃ₗ[ℝ] Matrix (Fin N) (Fin M) ℝ :=
    { toFun := fun A i j ↦ A (finProdFinEquiv (i, j))
      invFun := fun A ↦ toLp 2 (fun r ↦
        A (finProdFinEquiv.symm r).1 (finProdFinEquiv.symm r).2)
      left_inv := by
        intro A
        ext r
        change A (finProdFinEquiv (finProdFinEquiv.symm r)) = A r
        exact congrArg (fun s ↦ A s) (finProdFinEquiv.apply_symm_apply r)
      right_inv := by
        intro A
        ext i j
        change A (finProdFinEquiv.symm (finProdFinEquiv (i, j))).1
          (finProdFinEquiv.symm (finProdFinEquiv (i, j))).2 = A i j
        simp
      map_add' := by intro A B; ext i j; rfl
      map_smul' := by intro c A; ext i j; rfl }
  exact e.trans (Matrix.toEuclideanLin.trans LinearMap.toContinuousLinearMap)

#print axioms hilbertSchmidtCoordinateEquiv

end GlobalEmbedding.Paper
