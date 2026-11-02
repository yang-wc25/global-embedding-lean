import GlobalEmbedding.Paper.LittlePeriodicCAlphaBilinear
import GlobalEmbedding.Paper.HilbertSchmidtCoordinateNorm

/-!
# Actual Hilbert–Schmidt coefficient multiplication on little Hölder spaces

Source: `literature/parallelizable-stable-plus-one/main.tex`, `lem:balanced`, lines 396–402.
DAG node: `balanced-holder-multiplication-bounded`.
-/

namespace GlobalEmbedding.Paper

/-- For every k and 0<α<1, actual Hilbert–Schmidt coefficient multiplication is a bounded
bilinear map on the original little Hölder spaces, curried to a bounded linear multiplier map.

The coefficient model is faithful for ALL continuous linear value operators and its actual
Euclidean norm is exactly Hilbert–Schmidt, as the first two conclusions certify. Apply the
constructed actual little-space bilinear product to that value evaluation. Its exact values
are pointwise operator multiplication and its continuous bilinear norm bounds applications.
No coefficient-space multiplication data or extra source derivative is assumed.
Source: bounded coefficient multiplication in the proof of `lem:balanced`. -/
theorem balanced_holder_multiplication_bounded {a M N k : ℕ} {α : ℝ}
    (_hα0 : 0 < α) (hα1 : α < 1) :
    (∀ V : EuclideanSpace ℝ (Fin M) →L[ℝ] EuclideanSpace ℝ (Fin N),
      ∃! A : EuclideanSpace ℝ (Fin (N * M)), hilbertSchmidtCoordinateEvaluation M N A = V) ∧
    (∀ A : EuclideanSpace ℝ (Fin (N * M)), ‖A‖ ^ 2 = ∑ j : Fin M,
      ‖hilbertSchmidtCoordinateEvaluation M N A (EuclideanSpace.single j 1)‖ ^ 2) ∧
    ∃ mult : LittlePeriodicCAlphaFunction a (N * M) k α →L[ℝ]
        LittlePeriodicCAlphaFunction a M k α →L[ℝ] LittlePeriodicCAlphaFunction a N k α,
      (∀ (A : LittlePeriodicCAlphaFunction a (N * M) k α)
        (u : LittlePeriodicCAlphaFunction a M k α) (x : EuclideanSpace ℝ (Fin a)),
        (mult A u).val.toFun x =
          hilbertSchmidtCoordinateEvaluation M N (A.val.toFun x) (u.val.toFun x)) ∧
      (∃ C : ℝ, 0 ≤ C ∧ ∀ (A : LittlePeriodicCAlphaFunction a (N * M) k α)
        (u : LittlePeriodicCAlphaFunction a M k α),
        ‖mult A u‖ ≤ C * ‖A‖ * ‖u‖) := by
  refine ⟨?_, hilbertSchmidt_coordinate_norm M N, ?_⟩
  · intro V
    let e := hilbertSchmidtCoordinateEquiv M N
    refine ⟨e.symm V, e.apply_symm_apply V, ?_⟩
    intro A hA
    change e A = V at hA
    exact e.injective (hA.trans (e.apply_symm_apply V).symm)
  · let mult := littlePeriodicCAlphaBilinear (a := a) (k := k)
      (hilbertSchmidtCoordinateEvaluation M N) hα1.le
    refine ⟨mult, fun A u x ↦ rfl, ?_⟩
    let R := periodicCAlphaBilinearContinuous (a := a) (k := k)
      (hilbertSchmidtCoordinateEvaluation M N) hα1.le
    refine ⟨‖R‖, norm_nonneg R, ?_⟩
    intro A u
    change ‖R A.val u.val‖ ≤ ‖R‖ * ‖A.val‖ * ‖u.val‖
    exact ((R A.val).le_opNorm u.val).trans
      (mul_le_mul_of_nonneg_right (R.le_opNorm A.val) (norm_nonneg u.val))

#print axioms balanced_holder_multiplication_bounded

end GlobalEmbedding.Paper
