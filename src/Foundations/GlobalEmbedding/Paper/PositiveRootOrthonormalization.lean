import Mathlib.Analysis.InnerProductSpace.GramMatrix
import Mathlib.Analysis.Matrix.Order

/-!
# Positive-root orthonormalization preserves the frame span

Source: `literature/parallelizable-stable-plus-one/main.tex`, Proposition
`prop:initialization`, proof line 798. For a frame with Gram matrix `G`, the
normalized frame is obtained by multiplying its columns by `sqrt(G)⁻¹`.
-/

namespace GlobalEmbedding.Paper

open Matrix
open scoped MatrixOrder

/-- The explicit inverse positive Gram-root normalization is orthonormal and spans
exactly the original frame space. Its Gram matrix is `P⁻¹ * G * P⁻¹ = 1`, and
multiplication back by `P` reconstructs each original vector. No spanning or
finite-dimensionality assumption on the ambient space is needed; empty families
are included. Source: positive-root normalization in `prop:initialization`. -/
theorem positive_root_orthonormalization
    {n E : Type*} [Fintype n] [DecidableEq n]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    (v : n → E) (hv : LinearIndependent ℝ v) :
    let P := CFC.sqrt (Matrix.gram ℝ v)
    let e : n → E := fun i ↦ ∑ j, P⁻¹ j i • v j
    Orthonormal ℝ e ∧
      Submodule.span ℝ (Set.range e) = Submodule.span ℝ (Set.range v) ∧
      ∀ j, ∑ i, P i j • e i = v j := by
  dsimp only
  let G := Matrix.gram ℝ v
  let P := CFC.sqrt G
  let C := P⁻¹
  let e : n → E := fun i ↦ ∑ j, C j i • v j
  have hG : G.PosDef := Matrix.posDef_gram_of_linearIndependent hv
  have hP : P.PosDef := (IsStrictlyPositive.sqrt G hG.isStrictlyPositive).posDef
  have hC : C.PosDef := hP.inv
  have hPP : P * P = G := CFC.sqrt_mul_sqrt_self G hG.posSemidef.nonneg
  have hCP : C * P = 1 := Matrix.nonsing_inv_mul _ ((Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit)
  have hPC : P * C = 1 := Matrix.mul_nonsing_inv _ ((Matrix.isUnit_iff_isUnit_det P).mp hP.isUnit)
  have hcong : Cᴴ * G * C = 1 := by
    rw [hC.isHermitian.eq, ← hPP]
    calc
      C * (P * P) * C = (C * P) * (P * C) := by simp only [mul_assoc]
      _ = 1 := by rw [hCP, hPC, one_mul]
  have hon : Orthonormal ℝ e := by
    apply Matrix.gram_eq_one_iff_orthonormal.mp
    ext i j
    change inner ℝ (∑ a, C a i • v a) (∑ b, C b j • v b) = _
    rw [← Matrix.star_dotProduct_gram_mulVec]
    have hcong' : Cᴴ * (G * C) = 1 := by simpa only [mul_assoc] using hcong
    have hij := congrArg (fun Z : Matrix n n ℝ ↦ Z i j) hcong'
    simpa only [Matrix.mul_apply, Matrix.conjTranspose_apply, star_trivial,
      dotProduct, mulVec, Pi.star_apply, G] using hij
  have hrec (j : n) : ∑ i, P i j • e i = v j := by
    dsimp only [e]
    simp_rw [Finset.smul_sum, smul_smul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.sum_smul]
    have hc (k : n) : ∑ i, P i j * C k i = (C * P) k j := by
      simp only [Matrix.mul_apply, mul_comm]
    simp_rw [hc]
    simp [hCP, Matrix.one_apply, ite_smul]
  refine ⟨hon, ?_, hrec⟩
  apply le_antisymm
  · apply Submodule.span_le.mpr
    rintro _ ⟨i, rfl⟩
    exact Submodule.sum_mem _ (fun j _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self j)))
  · apply Submodule.span_le.mpr
    rintro _ ⟨j, rfl⟩
    rw [← hrec j]
    exact Submodule.sum_mem _ (fun i _ ↦ Submodule.smul_mem _ _
      (Submodule.subset_span (Set.mem_range_self i)))

#print axioms positive_root_orthonormalization

end GlobalEmbedding.Paper
