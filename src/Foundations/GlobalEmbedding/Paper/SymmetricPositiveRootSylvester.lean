import GlobalEmbedding.Paper.PositiveRootSylvester
import Mathlib.Algebra.Star.Module
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.Normed.Module.FiniteDimension

/-!
# The Sylvester equivalence on symmetric matrices

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, proof line 798. The actual Sylvester map preserves symmetric
matrices. Its full-space uniqueness implies that the unique inverse image of a
symmetric matrix is symmetric, giving a continuous linear equivalence on the native
self-adjoint submodule of real square matrices.
-/

namespace GlobalEmbedding.Paper

open Matrix
open scoped Matrix.Norms.L2Operator

/-- The actual derivative of matrix squaring at a positive matrix is a continuous
linear equivalence on the space of real symmetric matrices. To prove surjectivity,
solve the equation in the full matrix space. Taking adjoints gives another solution,
so full-space uniqueness forces the solution to be self-adjoint. Continuity follows
from finite dimensionality. Empty index types are included.
Source: `prop:initialization`, positive metric square-root argument. -/
theorem positive_symmetric_sylvester_equiv_exists
    {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    ∃ L : (selfAdjoint.submodule ℝ (Matrix n n ℝ)) ≃L[ℝ]
        (selfAdjoint.submodule ℝ (Matrix n n ℝ)),
      ∀ Z, (L Z : Matrix n n ℝ) = P * (Z : Matrix n n ℝ) + (Z : Matrix n n ℝ) * P := by
  let S := selfAdjoint.submodule ℝ (Matrix n n ℝ)
  let L : S →ₗ[ℝ] S :=
    { toFun := fun Z ↦ ⟨P * (Z : Matrix n n ℝ) + (Z : Matrix n n ℝ) * P, by
        change star (P * (Z : Matrix n n ℝ) + (Z : Matrix n n ℝ) * P) = _
        rw [star_add, star_mul, star_mul, hP.isHermitian.star_eq, Z.property]
        exact add_comm _ _⟩
      map_add' := by
        intro X Y
        apply Subtype.ext
        change P * ((X : Matrix n n ℝ) + Y) + ((X : Matrix n n ℝ) + Y) * P =
          (P * (X : Matrix n n ℝ) + (X : Matrix n n ℝ) * P) +
            (P * (Y : Matrix n n ℝ) + (Y : Matrix n n ℝ) * P)
        simp only [mul_add, add_mul]
        abel_nf
      map_smul' := by
        intro c X
        apply Subtype.ext
        change P * (c • (X : Matrix n n ℝ)) + (c • (X : Matrix n n ℝ)) * P =
          c • (P * (X : Matrix n n ℝ) + (X : Matrix n n ℝ) * P)
        simp only [mul_smul_comm, smul_mul_assoc, smul_add] }
  have hbij : Function.Bijective L := by
    constructor
    · intro X Y hXY
      apply Subtype.ext
      exact (positive_sylvester_bijective hP).injective (congrArg Subtype.val hXY)
    · intro W
      obtain ⟨Z, hZ⟩ := (positive_sylvester_bijective hP).surjective (W : Matrix n n ℝ)
      have hZstar : P * star Z + star Z * P = (W : Matrix n n ℝ) := by
        have h := congrArg star hZ
        change star (P * Z + Z * P) = star (W : Matrix n n ℝ) at h
        rw [star_add, star_mul, star_mul, hP.isHermitian.star_eq, W.property] at h
        simpa only [add_comm] using h
      have hs : star Z = Z := (positive_sylvester_bijective hP).injective (hZstar.trans hZ.symm)
      refine ⟨⟨Z, hs⟩, ?_⟩
      apply Subtype.ext
      exact hZ
  exact ⟨(LinearEquiv.ofBijective L hbij).toContinuousLinearEquiv, fun _ ↦ rfl⟩

#print axioms positive_symmetric_sylvester_equiv_exists

end GlobalEmbedding.Paper
