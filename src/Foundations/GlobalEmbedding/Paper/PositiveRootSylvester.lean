import Mathlib.Analysis.Matrix.PosDef

/-!
# Sylvester invertibility for positive real matrices

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, proof line 798. The derivative of the matrix square map is
`Z ↦ P * Z + Z * P`. An orthogonal eigenbasis of the positive matrix `P` turns this
operator into entrywise multiplication by the strictly positive numbers `eig i + eig j`.
-/

namespace GlobalEmbedding.Paper

open Matrix

/-- The Sylvester operator associated to a real positive-definite matrix is bijective.
The proof diagonalizes `P` orthogonally and divides each matrix entry by the sum
of the two positive eigenvalues. It also applies to empty index types.
Source: Proposition `prop:initialization`, positive metric square-root argument. -/
theorem positive_sylvester_bijective
    {n : Type*} [Fintype n] [DecidableEq n] {P : Matrix n n ℝ} (hP : P.PosDef) :
    Function.Bijective (fun Z : Matrix n n ℝ ↦ P * Z + Z * P) := by
  let eig := hP.isHermitian.eigenvalues
  let D : Matrix n n ℝ := diagonal eig
  let e := Unitary.conjStarAlgAut ℝ (Matrix n n ℝ) hP.isHermitian.eigenvectorUnitary
  have heD : e D = P := by
    simpa [e, D, eig, Function.comp_def] using hP.isHermitian.spectral_theorem.symm
  have he (Z : Matrix n n ℝ) : e (D * Z + Z * D) = P * e Z + e Z * P := by
    simp only [map_add, map_mul, heD]
  have hd (Z : Matrix n n ℝ) (i j : n) :
      (D * Z + Z * D) i j = (eig i + eig j) * Z i j := by
    simp only [D, Matrix.add_apply, diagonal_mul, mul_diagonal]
    ring
  have heig (i j : n) : eig i + eig j ≠ 0 :=
    ne_of_gt (add_pos (hP.eigenvalues_pos i) (hP.eigenvalues_pos j))
  constructor
  · intro X Y hXY
    obtain ⟨X', rfl⟩ := e.surjective X
    obtain ⟨Y', rfl⟩ := e.surjective Y
    apply congrArg e
    have h := e.injective ((he X').trans (hXY.trans (he Y').symm))
    ext i j
    have hij := congrArg (fun Z : Matrix n n ℝ ↦ Z i j) h
    rw [hd, hd] at hij
    exact mul_left_cancel₀ (heig i j) hij
  · intro W
    let V := e.symm W
    let Z : Matrix n n ℝ := fun i j ↦ V i j / (eig i + eig j)
    refine ⟨e Z, ?_⟩
    change P * e Z + e Z * P = W
    rw [← he]
    have hDZ : D * Z + Z * D = V := by
      ext i j
      rw [hd]
      exact mul_div_cancel₀ (V i j) (heig i j)
    rw [hDZ]
    exact e.apply_symm_apply W

#print axioms positive_sylvester_bijective

end GlobalEmbedding.Paper
